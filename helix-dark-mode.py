#!/usr/bin/python3
# Copyright Sebastian Wiesner <sebastian@swsnr.de>
#
# Licensed under the EUPL 1.2

import asyncio
from functools import partial
import logging
import os
import tempfile
from signal import Signals, pidfd_send_signal
from contextlib import contextmanager
from enum import Enum
from pathlib import Path
from typing import Any, Generator, Tuple, cast
from concurrent.futures import ThreadPoolExecutor, Executor

from gi.events import GLibEventLoopPolicy  # type: ignore
from gi.repository import GLib, Gio  # type: ignore


LOG: logging.Logger = logging.getLogger("helix-dark-mode")

XDG_CONFIG_HOME: Path = Path(os.environ.get("XDG_CONFIG_HOME", Path.home() / ".config"))

OUR_PID: int = os.getpid()


@contextmanager
def open_directory(name: str, dir_fd: int | None) -> Generator[int]:
    """Open a directory as file descriptor.

    Return a file descriptor for the directory referred to by `name`.

    `dir_fd` may be a FD referring to the parent directory, in this case `name`
    must be relative to that parent directory.

    Otherwise `name` may be either relative to the current working directory or
    absolute.
    """
    fd = os.open(name, os.O_DIRECTORY | os.O_RDONLY, dir_fd=dir_fd)
    yield fd
    os.close(fd)


def is_matching_process(pidfd: int, name: str) -> bool:
    """Whether a process matches a name.

    Return `True` if the process referred to by the given PID file descriptor,
    that is, a directory FD to a process directory under `/proc`, matches the
    given `name`, or `False` otherwise.

    Check `name` against the basename of the process executable, referred to by
    the `/proc/<PID>/exe` symlink, and against the basename of the first item in
    the process command line as contained in `/proc/<PID>/cmdline`.
    """
    target = os.readlink("exe", dir_fd=pidfd)
    if os.path.basename(target) == name:
        return True

    with os.fdopen(os.open("cmdline", os.O_RDONLY, dir_fd=pidfd)) as cmdline:
        if os.path.basename(cmdline.read().split("\0")[0]) == name:
            return True

    return False


def send_signal_to_matching_processes(name: str, signal: Signals) -> None:
    """Send a signal to all processes matching a certain name."""
    with open_directory("/proc", dir_fd=None) as procfd:
        with os.scandir(procfd) as proc_dentries:
            for dentry in proc_dentries:
                if not dentry.name.isdigit():  # Not a PID
                    continue
                if dentry.name == str(OUR_PID):  # Our own process
                    LOG.debug("Skipping %s, our own process", dentry.path)
                    continue
                if not dentry.is_dir():  # Not a PID directory
                    continue

                LOG.debug("Checking process %s", dentry.name)
                try:
                    with open_directory(dentry.name, dir_fd=procfd) as pidfd:
                        if is_matching_process(pidfd, name):
                            LOG.info(
                                "%s matches %s, sending signal %s to %s",
                                dentry.name,
                                signal.name,
                                name,
                            )
                            pidfd_send_signal(pidfd, signal)
                except Exception as error:
                    if isinstance(error, PermissionError):
                        # EPERM is frequent in /proc, so let's not log these
                        continue
                    LOG.warning(
                        "Skipping %s, failed: %s", dentry.name, error, exc_info=True
                    )


class ColorScheme(Enum):
    # See https://flatpak.github.io/xdg-desktop-portal/docs/doc-org.freedesktop.portal.Settings.html
    NO_PREFERENCE = 0
    PREFER_DARK = 1
    PREFER_LIGHT = 2


def theme_for_color_scheme(color_scheme: ColorScheme) -> str:
    match color_scheme:
        case ColorScheme.NO_PREFERENCE:
            return "default"
        case ColorScheme.PREFER_DARK:
            return "dark"
        case ColorScheme.PREFER_LIGHT:
            return "light"


def apply_color_scheme(color_scheme: ColorScheme) -> None:
    theme_directory = XDG_CONFIG_HOME / "helix" / "themes"
    theme = theme_for_color_scheme(color_scheme)
    if not (theme_directory / theme).with_suffix(".toml").exists():
        theme = "default"

    theme_file = (theme_directory / theme).with_suffix(".toml")
    if theme_file.exists():
        LOG.info("Re-linking auto.toml to %s", theme_file)
        auto_tmp = Path(tempfile.mktemp(prefix=".auto", dir=theme_directory))
        LOG.debug("Linking %s to %s", theme_file.name, auto_tmp)
        auto_tmp.symlink_to(theme_file.name)
        LOG.debug("Renaming %s to auto.toml", auto_tmp)
        auto_tmp.rename(theme_directory / "auto.toml")

        signal = Signals.SIGUSR1
        LOG.info("Sending %s to all helix processes", signal.name)
        send_signal_to_matching_processes("helix", signal)


async def process_color_scheme(
    apply_scheme_pool: Executor, color_schemes: asyncio.Queue[ColorScheme]
) -> None:
    try:
        while True:
            color_scheme = await color_schemes.get()
            apply_scheme_pool.submit(apply_color_scheme, color_scheme)
    except asyncio.QueueShutDown:
        LOG.info("Queue for color scheme changes shut down, stopping")


async def monitor_changed_settings(
    quit_event: asyncio.Event, color_schemes: asyncio.Queue[ColorScheme]
) -> None:
    """Monitor for color scheme changes.

    Connect to the Settings Desktop Portal via D-Bus, and listen for changes to
    the `color-scheme` setting in the `org.freedesktop.appearance` interface.

    Whenever the setting changed, put its current value into the `color_schemes`
    queue, without waiting.

    Continue until `quit_event` is triggered.
    """
    # Keep track of the scheme, to prevent updates if the theme didn't change
    last_color_scheme: int | None = None

    def _handle_setting_changed(_c, _s, _o, _i, _sig, args: GLib.Variant) -> None:  # type: ignore
        nonlocal last_color_scheme
        args = args.unpack()  # type: ignore
        (iface, key, value) = cast(Tuple[str, str, Any], args)
        LOG.debug("SettingChanged %s %s %s", iface, key, value)
        if iface == "org.freedesktop.appearance" and key == "color-scheme":
            value = cast(int, value)
            if value != last_color_scheme:
                last_color_scheme = value
                scheme = ColorScheme(value)
                LOG.info("Color scheme changed to %s", scheme)
                color_schemes.put_nowait(scheme)
            else:
                LOG.info("Color scheme did not change from previous value")

    connection = await Gio.bus_get(Gio.BusType.SESSION)  # type: ignore
    signal_subscription = connection.signal_subscribe(  # type: ignore
        "org.freedesktop.portal.Desktop",
        "org.freedesktop.portal.Settings",
        "SettingChanged",
        "/org/freedesktop/portal/desktop",
        # Only listen to changes of appearance settings
        "org.freedesktop.appearance",
        Gio.DBusSignalFlags.MATCH_ARG0_NAMESPACE,  # type: ignore
        _handle_setting_changed,
    )

    try:
        # Receive the initial scheme
        response = await connection.call(  # type: ignore
            "org.freedesktop.portal.Desktop",
            "/org/freedesktop/portal/desktop",
            "org.freedesktop.portal.Settings",
            "ReadOne",
            GLib.Variant("(ss)", ("org.freedesktop.appearance", "color-scheme")),  # type: ignore
            GLib.VariantType("(v)"),  # type: ignore
            Gio.DBusCallFlags.NO_AUTO_START,  # type: ignore
            1000,
            None,
        )
        response = response.unpack()  # type: ignore
        (value,) = cast(Tuple[Any], response)
        if not isinstance(value, int):
            raise ValueError(
                f"Unexpected value for color-scheme, expected number, but got {value}"
            )
        last_color_scheme = value
        color_schemes.put_nowait(ColorScheme(value))
    except Exception as error:
        LOG.error(
            "Failed to receive current value of color-scheme: %s", error, exc_info=True
        )

    LOG.debug("Waiting until terminate")
    # Wait forever for an event we never trigger, to effectively keep running forever
    await quit_event.wait()
    LOG.debug("Asked to quit, disconnecting signals and closing D-Bus connection")
    connection.signal_unsubscribe(signal_subscription)  # type: ignore
    await connection.close()  # type: ignore


def quit_on_signal(event: asyncio.Event, signal: Signals) -> None:
    LOG.info("Received %s, quitting", signal.name)
    event.set()


async def close_queue_when_quit(
    quit_event: asyncio.Event, queue: asyncio.Queue[Any]
) -> None:
    await quit_event.wait()
    LOG.debug("Asked to quit, shutting down queue for color scheme changes")
    queue.shutdown()


def main() -> None:
    """Monitor the desktop color scheme and update Helix' color theme accordingly."""
    logging.basicConfig(level=logging.DEBUG)

    policy = GLibEventLoopPolicy()
    asyncio.set_event_loop_policy(policy)
    loop = cast(asyncio.EventLoop, policy.get_event_loop())

    quit_event = asyncio.Event()
    apply_scheme_pool = ThreadPoolExecutor(
        max_workers=1, thread_name_prefix="apply-color-scheme-"
    )
    color_schemes: asyncio.Queue[ColorScheme] = asyncio.Queue()

    for signal in [Signals.SIGTERM, Signals.SIGINT]:
        loop.add_signal_handler(signal, quit_on_signal, quit_event, signal)
    loop.create_task(close_queue_when_quit(quit_event, color_schemes))
    loop.create_task(process_color_scheme(apply_scheme_pool, color_schemes))
    loop.run_until_complete(monitor_changed_settings(quit_event, color_schemes))


if __name__ == "__main__":
    try:
        main()
    finally:
        logging.shutdown()
