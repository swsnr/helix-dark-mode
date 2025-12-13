// Copyright Sebastian Wiesner <sebastian@swsnr.de>
//
// Licensed under the EUPL 1.2

#![deny(warnings, clippy::all, clippy::pedantic,
    // Do cfg(test) right
    clippy::cfg_not_test,
    clippy::tests_outside_test_module,
    // Guard against left-over debugging output
    clippy::dbg_macro,
    clippy::print_stderr,
    clippy::print_stdout,
    clippy::unimplemented,
    clippy::use_debug,
    clippy::todo,
    // We shouldn't exit hard with Tokio
    clippy::exit,
    // Don't panic carelessly
    clippy::get_unwrap,
    clippy::unused_result_ok,
    clippy::unwrap_in_result,
    clippy::indexing_slicing,
    // Do not carelessly ignore errors
    clippy::let_underscore_must_use,
    // Code smells
    clippy::float_cmp_const,
    clippy::if_then_some_else_none,
)]
#![forbid(unsafe_code)]

//! Automatic dark mode switching for [Helix](https://helix-editor.com).

use std::ffi::OsStr;
use std::fs::File;
use std::io::{BufReader, ErrorKind, Read};
use std::os::fd::AsFd;
use std::os::unix::ffi::OsStrExt;
use std::os::{fd::BorrowedFd, unix::fs::symlink};
use std::path::Path;

use anyhow::Context;
use async_channel::{Receiver, Sender};
use async_executor::LocalExecutor;
use async_signal::Signals;
use futures_lite::{Stream, StreamExt as _, stream};
use logcontrol_tracing::{PrettyLogControl1LayerFactory, TracingLogControl1};
use logcontrol_zbus::{ConnectionBuilderExt as _, logcontrol::LogControl1};
use rustix::fs::{DirEntry, readlinkat};
use rustix::io::Errno;
use rustix::process::pidfd_send_signal;
use rustix::{
    fs::{Dir, FileType, Mode, OFlags, openat},
    path::Arg,
    process::{Signal, getpid},
};
use tracing::{Instrument, Level, Span, debug, error, info, info_span, instrument, trace, warn};
use tracing_subscriber::{Registry, layer::SubscriberExt as _};
use zbus::{
    proxy,
    zvariant::{self, OwnedValue},
};

/// XDG Settings portal.
///
/// See <https://flatpak.github.io/xdg-desktop-portal/docs/doc-org.freedesktop.portal.Settings.html>
#[proxy(
    default_service = "org.freedesktop.portal.Desktop",
    default_path = "/org/freedesktop/portal/desktop",
    interface = "org.freedesktop.portal.Settings",
    gen_blocking = false
)]
trait Settings {
    /// See <https://flatpak.github.io/xdg-desktop-portal/docs/doc-org.freedesktop.portal.Settings.html#org-freedesktop-portal-settings-settingchanged>
    #[zbus(signal)]
    fn setting_changed(
        &self,
        namespace: &str,
        key: &str,
        value: zbus::zvariant::Value<'_>,
    ) -> zbus::fdo::Result<()>;

    /// See <https://flatpak.github.io/xdg-desktop-portal/docs/doc-org.freedesktop.portal.Settings.html#org-freedesktop-portal-settings-readone>
    #[zbus(no_autostart)]
    fn read_one(&self, namespace: &str, key: &str) -> zbus::fdo::Result<OwnedValue>;
}

/// Desktop color scheme preference.
///
/// See <https://flatpak.github.io/xdg-desktop-portal/docs/doc-org.freedesktop.portal.Settings.html>.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum ColorScheme {
    NoPreference,
    PreferDark,
    PreferLight,
}

impl TryFrom<&zvariant::Value<'_>> for ColorScheme {
    type Error = zvariant::Error;

    fn try_from(value: &zvariant::Value<'_>) -> Result<Self, Self::Error> {
        match u32::try_from(value)? {
            // See https://flatpak.github.io/xdg-desktop-portal/docs/doc-org.freedesktop.portal.Settings.html
            // for these values
            0 => Ok(Self::NoPreference),
            1 => Ok(Self::PreferDark),
            2 => Ok(Self::PreferLight),
            _ => Err(zvariant::Error::OutOfBounds),
        }
    }
}

/// Setup logging.
///
/// Set up logging to log to journald directly if the process runs under systemd.
///
/// When running interactively set up pretty-formatted console logging with a
/// standard `$RUST_LOG` environment filter.  If the env filter is active default
/// to [`Level::INFO`] in release builds, and [`Level::DEBUG`] level in debug
/// builds, i.e. under `cfg!(debug_assertions)`.
///
/// In either case, wrap a [`LogControl1`] layer around the logging setup and
/// return it, for exporting over D-Bus to change log level and log target
/// dynamically at runtime.
fn setup_logging() -> impl LogControl1 {
    // Setup env filter for convenient log control on console
    let env_filter = tracing_subscriber::EnvFilter::try_from_default_env().ok();
    // If an env filter is set with $RUST_LOG use the lowest level as default for the control part,
    // to make sure the env filter takes precedence initially.
    let default_level = if env_filter.is_some() {
        Level::TRACE
    } else if cfg!(debug_assertions) {
        // In debug builds, e.g. local testing, log more by default
        Level::DEBUG
    } else {
        Level::INFO
    };
    let (control, control_layer) =
        TracingLogControl1::new_auto(PrettyLogControl1LayerFactory, default_level).unwrap();
    let subscriber = Registry::default().with(env_filter).with(control_layer);
    tracing::subscriber::set_global_default(subscriber).unwrap();
    control
}

/// Get the current desktop color scheme.
///
/// Read the `color-scheme` setting from `settings`, and deserialize the return
/// value.
#[instrument(skip(settings))]
async fn get_color_scheme(settings: SettingsProxy<'_>) -> zbus::fdo::Result<ColorScheme> {
    info!("Requesting current color scheme from Desktop Settings Portal");
    let response = settings
        .read_one("org.freedesktop.appearance", "color-scheme")
        .await?;
    ColorScheme::try_from(&*response)
        .map_err(|error| zbus::fdo::Error::ZBus(zbus::Error::Variant(error)))
}

/// Whether a process matches a name.
///
/// Determine whether the process referred to by `pid_fd` matches the given `name`,
/// either in the file name of the executable that launched the process (as per
/// `/proc/<PID>/exe`) or the first element of the process command line (as per
/// `/proc/<PID>/cmdline`).
///
/// Return `true` if the process matches, or `false` otherwise.
///
/// # Errors
///
/// Fail if reading the `exe` symlink or the `cmdline` file fail.
fn process_matches_name(pid_fd: BorrowedFd, name: &str) -> anyhow::Result<bool> {
    let exe_target = readlinkat(pid_fd, "exe", Vec::new())
        .with_context(|| "Failed to read exe symlink target")?;
    if Path::new(OsStr::from_bytes(exe_target.as_bytes()))
        .file_name()
        .map(OsStrExt::as_bytes)
        .is_some_and(|n| n == name.as_bytes())
    {
        return Ok(true);
    }

    let cmdline_name = BufReader::new(File::from(
        openat(
            pid_fd,
            "cmdline",
            OFlags::RDONLY | OFlags::CLOEXEC,
            Mode::empty(),
        )
        .with_context(|| "Failed to open cmdline")?,
    ))
    .bytes()
    .take_while(|b| b.as_ref().is_ok_and(|b| *b != 0))
    .collect::<std::io::Result<Vec<_>>>()
    .with_context(|| "Failed to read from cmdline")?;

    Ok(Path::new(OsStr::from_bytes(&cmdline_name))
        .file_name()
        .map(OsStrExt::as_bytes)
        .is_some_and(|n| n == name.as_bytes()))
}

/// Send a signal to a matching process.
///
/// `proc_fd` is a dir fd for `/proc`, and `dentry` the directory entry within
/// `/proc` to check.
///
/// Match the process referred to by `dentry` against `name` using
/// [`process_matches_name`], and if it matches, send the given `signal` to
/// the process.
///
/// Carefully use PID FDs to make sure that there are no race conditions.
#[instrument(skip_all, fields(pid = ?dentry.file_name(), name, ?signal))]
fn send_signal_to_matching_process(
    proc_fd: BorrowedFd,
    dentry: &DirEntry,
    name: &str,
    signal: Signal,
) -> anyhow::Result<()> {
    let pid_fd = openat(
        proc_fd,
        dentry.file_name(),
        OFlags::DIRECTORY | OFlags::RDONLY | OFlags::CLOEXEC | OFlags::NOFOLLOW,
        Mode::empty(),
    )
    .with_context(|| {
        format!(
            "Failed to open subdirectory {:?} of /proc",
            dentry.file_name()
        )
    })?;
    match process_matches_name(pid_fd.as_fd(), name) {
        Ok(matches) => {
            if matches {
                info!("Sending {signal:?} to {:?}", dentry.file_name());
                pidfd_send_signal(pid_fd, signal).with_context(|| {
                    format!("Failed to send {signal:?} to {:?}", dentry.file_name())
                })?;
            } else {
                trace!("Skipping {:?}, doesn't match {name}", dentry.file_name());
            }
            Ok(())
        }
        Err(error) => {
            // Do not log certain expected errors
            if error.downcast_ref::<Errno>().is_some_and(|e| {
                matches!(e.kind(), ErrorKind::PermissionDenied | ErrorKind::NotFound)
            }) {
                return Ok(());
            }
            Err(error.context(format!("Failed to check name of {:?}", dentry.file_name())))
        }
    }
}

/// Send a signal to all processes matching a name.
///
/// Iterate through all processes, match each process againt `name` using
/// [`process_matches_name`], and if so, send `signal` to that process.
/// Ignore (but log) any errors along the way.
///
/// Carefully use directory FDs and PID FDs to make sure that there are no race conditions.
fn send_signal_to_matching_processes(name: &str, signal: Signal) -> anyhow::Result<()> {
    let proc_fd = rustix::fs::open(
        "/proc",
        OFlags::DIRECTORY | OFlags::RDONLY | OFlags::CLOEXEC | OFlags::NOFOLLOW,
        Mode::empty(),
    )
    .with_context(|| "Failed to open /proc")?;
    let pid_self = getpid().as_raw_nonzero().to_string();
    for dentry_res in Dir::read_from(&proc_fd).with_context(|| "Failed to read /proc")? {
        let dentry = match dentry_res {
            Ok(dentry) => dentry,
            Err(err) => {
                warn!("Skipping failed dentry in /proc: {err}");
                continue;
            }
        };
        let span = info_span!("process", pid = ?dentry.file_name());
        let _guard = span.enter();

        if dentry.file_type() != FileType::Directory {
            continue;
        }
        if dentry.file_name().to_bytes() == b".." || dentry.file_name().to_bytes() == b"." {
            continue;
        }
        if dentry.file_name().as_str().unwrap_or_default() == pid_self {
            // Skip over our own process
            continue;
        }
        if let Err(error) = send_signal_to_matching_process(proc_fd.as_fd(), &dentry, name, signal)
        {
            warn!(
                "Skipping over {}, failed: {error:#}",
                dentry.file_name().to_string_lossy()
            );
        }
    }
    Ok(())
}

/// Reload helix whenever asked to.
///
/// Whenever `reload_rx` receives a new value, send `SIGUSR1` to all processes
/// named `helix`, to ask helix to reload its configuration.
async fn reload_helix(reload_rx: Receiver<tracing::Span>) {
    while let Ok(span) = reload_rx.recv().await {
        let _guard = span.enter();
        let span = Span::current();
        let result = blocking::unblock(move || {
            span.in_scope(|| send_signal_to_matching_processes("helix", Signal::USR1))
        })
        .in_current_span()
        .await;
        match result {
            Ok(()) => {
                info!("Successfully reloaded all Helix processes");
            }
            Err(error) => {
                error!("Failed to reload helix processes: {error:#}");
            }
        }
    }
}

/// Update the helix theme according to a color scheme.
///
/// Map `color_scheme` to either `default.toml`, `dark.toml`, or `light.toml`,
/// and atomically symlink `auto.toml` to the respective theme file.  If either
/// `dark.toml` or `light.toml` do not exist, fall back to `default.toml`.
///
/// If `default.toml` doesn't exist as well, log a warning.
#[instrument]
fn update_helix_theme(color_scheme: ColorScheme) -> anyhow::Result<()> {
    let theme_dir = std::env::var_os("XDG_CONFIG_HOME")
        .map_or_else(|| std::env::home_dir().unwrap().join(".config"), Into::into)
        .join("helix")
        .join("themes");
    let mut theme = match color_scheme {
        ColorScheme::NoPreference => "default",
        ColorScheme::PreferDark => "dark",
        ColorScheme::PreferLight => "light",
    };
    if !std::fs::exists(theme_dir.join(theme).with_extension("toml")).unwrap_or_default() {
        info!("Theme {theme} does not exist, falling back to default");
        theme = "default";
    }

    let theme_file = theme_dir.join(theme).with_extension("toml");
    if std::fs::exists(&theme_file).unwrap_or_default() {
        info!("Re-linking auto.toml to {}", theme_file.display());
        let auto_tmp = theme_dir.join(format!(
            ".auto-{}.toml",
            std::iter::from_fn(|| Some(fastrand::alphanumeric()))
                .take(10)
                .collect::<String>(),
        ));
        debug!("Linking {} to {}", theme_file.display(), auto_tmp.display());
        // Create a relative symlink to the theme file
        symlink(theme_file.file_name().unwrap(), &auto_tmp).with_context(|| {
            format!(
                "Failed to link {} to {}",
                theme_file.display(),
                auto_tmp.display(),
            )
        })?;
        let auto = theme_dir.join("auto.toml");
        debug!("Renaming {} to {}", auto_tmp.display(), auto.display());
        std::fs::rename(&auto_tmp, &auto).with_context(|| {
            format!(
                "Failed to rename {} to {}",
                auto_tmp.display(),
                auto.display()
            )
        })?;
    } else {
        warn!(
            "Theme file {} does not exist, not updating auto.toml",
            theme_file.display()
        );
    }

    Ok(())
}

/// Receive color scheme updates and update the helix theme accordingly.
///
/// Loop over color schemes received from `color_scheme` and then spawn a
/// blocking [`update_helix_theme`] task.  When this task returns an error or
/// panics log the error and continue with the next element.
///
/// When the task succeeds notify `reload_helix_tx` to
///
/// Return once the `color_scheme` channel is closed.
async fn update_helix_theme_for_color_schemes(
    color_scheme_rx: Receiver<(ColorScheme, tracing::Span)>,
    reload_helix_tx: Sender<tracing::Span>,
) {
    while let Ok((color_scheme, span)) = color_scheme_rx.recv().await {
        let _guard = span.enter();
        let span = Span::current();
        let result = blocking::unblock(move || span.in_scope(|| update_helix_theme(color_scheme)))
            .in_current_span()
            .await;
        match result {
            Ok(()) => {
                info!("Triggering reload of all helix processs");
                if reload_helix_tx.force_send(Span::current()).is_err() {
                    warn!("No longer reloading helix processes, receiver unexpectedly closed");
                }
            }
            Err(error) => {
                error!("Failed to update the helix theme: {error:#}");
            }
        }
    }
}

/// Receive color scheme changes.
///
/// Request the current color scheme immediately, and then receive setting
/// changed signals for the color scheme setting.
///
/// Also, explicitly request the current color scheme when SIGUSR1 is received,
/// or if the name owner of the XDG Desktop Portal service changes.
///
/// Return a stream which yields the color scheme and a tracing span to use for
/// logging actions in response to the new color scheme.
async fn receive_color_scheme_changes(
    settings: SettingsProxy<'_>,
) -> anyhow::Result<impl Stream<Item = anyhow::Result<(Span, ColorScheme)>> + Unpin> {
    // Start listening for color scheme changes
    let color_scheme_signals = settings
        .receive_setting_changed_with_args(&[
            (0, "org.freedesktop.appearance"),
            (1, "color-scheme"),
        ])
        .await?
        .map(|setting_changed| {
            let args = setting_changed
                .args()
                .with_context(|| "Failed to get arguments of setting")?;
            (args.namespace == "org.freedesktop.appearance" && args.key == "color-scheme")
                .then(|| {
                    ColorScheme::try_from(&args.value)
                        .with_context(|| format!("Invalid color scheme: {:?}", args.value))
                })
                .transpose()
        })
        .filter_map(Result::transpose)
        // For some reason the Gnome XDG settings portal emits this signal
        // twice for every dark mode switch, so we filter out duplicates.
        // We can probably do this in a more elegant way than this scan/filter_map
        // combination, but this works, so why bother.
        .scan(None, |state, value| {
            Some(value.map(|value| {
                if Some(value) == state.take() {
                    None
                } else {
                    *state = Some(value);
                    Some(value)
                }
            }))
        })
        .filter_map(|value| {
            value.transpose().map(|res| {
                res.map(|color_scheme| {
                    let span = info_span!("desktop-setting-changed").entered();
                    info!(
                        color_scheme = ?color_scheme,
                        "org.freedesktop.appearance color-scheme changed to {color_scheme:?}"
                    );
                    (span.exit(), color_scheme)
                })
            })
        });

    // Explicitly refresh color scheme initially
    let initial_color_scheme = stream::once_future(Box::pin(get_color_scheme(settings.clone())))
        .filter(|result| match result {
            Err(zbus::fdo::Error::NameHasNoOwner(_)) => {
                warn!("xdg-portal-service not available");
                false
            }
            _ => true,
        })
        .map(|result| {
            result
                .with_context(|| "Failed to get color-scheme")
                .map(|color_scheme| (info_span!("initial-refresh"), color_scheme))
        });

    // Request the color scheme if the service name owner changed
    let portal_service_changed = settings
        .inner()
        .receive_owner_changed()
        .await?
        .filter_map(|v| {
            v.map(|name| {
                let span = info_span!("portal-service-changed").entered();
                info!("XDG Portal Service changed: {name}");
                span.exit()
            })
        });

    // Explicitly refresh color scheme on SIGUSR1
    let explicit_color_scheme_change = Signals::new([async_signal::Signal::Usr1])?
        .filter_map(Result::ok)
        .map(|_| {
            let span = info_span!("color-scheme-update-requested").entered();
            info!("Received SIGUSR1");
            span.exit()
        });

    let requested_color_scheme = explicit_color_scheme_change
        .or(portal_service_changed)
        .then(move |span| {
            let settings = settings.clone();
            let f = async move {
                let scheme = get_color_scheme(settings).await?;
                Ok((Span::current(), scheme))
            }
            .instrument(span);
            Box::pin(f)
        });

    Ok(initial_color_scheme.chain(color_scheme_signals.or(requested_color_scheme)))
}

async fn tick_connection(connection: zbus::Connection) {
    loop {
        connection.executor().tick().await;
    }
}

fn main() -> anyhow::Result<()> {
    let logcontrol = setup_logging();
    let executor = LocalExecutor::new();

    async_io::block_on(executor.run(async {
        let terminate = Signals::new([async_signal::Signal::Term, async_signal::Signal::Int])
            .with_context(|| "Failed to setup Unix signals")?
            .filter_map(|signal| {
                signal
                    .inspect_err(|error| {
                        warn!("Signal failed: {error}");
                    })
                    .ok()
            })
            .inspect(|signal| {
                info!("Received termination signal {signal:?}, terminating");
            })
            .take(1);

        let connection = zbus::connection::Builder::session()?
            .internal_executor(false)
            .serve_log_control(logcontrol_zbus::LogControl1::new(logcontrol))?
            .replace_existing_names(false)
            .allow_name_replacements(false)
            .name("de.swsnr.helix-dark-mode")?
            .build()
            .await?;
        let connection_loop = executor.spawn(tick_connection(connection.clone()));

        info!("Connected to bus");
        let settings = SettingsProxy::builder(&connection)
            .cache_properties(proxy::CacheProperties::No)
            .build()
            .await?;

        // Establish communication channels between different tasks
        let (color_scheme_tx, color_scheme_rx) = async_channel::bounded(5);
        let (reload_helix_tx, reload_helix_rx) = async_channel::bounded(1);

        // Spawn auxilliary tasks to update the helix theme and reload helix processes
        info!("Starting to update the helix theme according to the current color scheme");
        let update_theme_task = executor.spawn(update_helix_theme_for_color_schemes(
            color_scheme_rx,
            reload_helix_tx,
        ));
        let reload_helix_task = executor.spawn(reload_helix(reload_helix_rx));

        info!("Starting to watch for changes to the desktop color scheme");
        let color_scheme = stream::stop_after_future(
            receive_color_scheme_changes(settings).await?,
            terminate.last(),
        );
        let color_scheme_result = color_scheme
            .enumerate()
            .try_for_each(move |(n, res)| {
                let n = n + 1;
                let (span, color_scheme) = res?;
                let span = info_span!(
                    parent: &span, "color-scheme-update",
                 n = n, color_scheme = ?color_scheme
                )
                .entered();
                info!(
                    n,
                    ?color_scheme,
                    "Color scheme changed {n}th time, to {color_scheme:?}",
                );
                let span = span.exit();
                color_scheme_tx
                    .force_send((color_scheme, span))
                    .with_context(|| "Color theme channel closed unexpectedly")?;
                Ok(())
            })
            .await;

        info!("Stopped listing for color scheme changes, waiting for pending tasks");
        connection_loop.cancel().await;

        // Then wait until all auxilliary tasks have completed, with their inbound
        // channels being closed
        update_theme_task.await;
        reload_helix_task.await;

        info!("Good bye");
        color_scheme_result
    }))
}
