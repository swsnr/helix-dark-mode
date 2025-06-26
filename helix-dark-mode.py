#!/usr/bin/python3
# Copyright Sebastian Wiesner <sebastian@swsnr.de>
#
# Licensed under the EUPL 1.2

import asyncio
import logging
from enum import Enum
from typing import Any, Tuple, cast
from concurrent.futures import ThreadPoolExecutor, Executor

from gi.events import GLibEventLoopPolicy  # type: ignore
from gi.repository import Gio  # type: ignore


LOG = logging.getLogger("helix-dark-mode")


class ColorScheme(Enum):
    # See https://flatpak.github.io/xdg-desktop-portal/docs/doc-org.freedesktop.portal.Settings.html
    NO_PREFERENCE = 0
    PREFER_DARK = 1
    PREFER_LIGHT = 2


def apply_color_scheme(color_scheme: ColorScheme) -> None:
    # TODO: Apply color scheme and send USR1 all helix processes
    print("Color scheme changed", color_scheme)


async def process_color_scheme(
    apply_scheme_pool: Executor, color_schemes: asyncio.Queue[ColorScheme]
) -> None:
    while True:
        color_scheme = await color_schemes.get()
        apply_scheme_pool.submit(apply_color_scheme, color_scheme)


class SettingChangedHandler:
    def __init__(self, current_theme: asyncio.Queue[ColorScheme]):
        self._current_theme = current_theme
        self._last_theme: int | None = None

    def __call__(
        self,
        _connection,  # type: ignore
        _sender: str,
        _objpath: str,
        _iface: str,
        _signal: str,
        args,  # type: ignore
    ) -> None:
        args = args.unpack()  # type: ignore
        (iface, key, value) = cast(Tuple[str, str, Any], args)
        LOG.debug("SettingChanged %s %s %s", iface, key, value)
        if iface == "org.freedesktop.appearance" and key == "color-scheme":
            value = cast(int, value)
            if value != self._last_theme:
                self._last_theme = value
                scheme = ColorScheme(value)
                LOG.info("Color scheme changed to %s", scheme)
                self._current_theme.put_nowait(scheme)
            else:
                LOG.info("Color scheme did not change from previous value")


async def monitor_changed_settings(color_schemes: asyncio.Queue[ColorScheme]) -> None:
    # We use an event to wait "forever", so as to keep a reference to the
    # connection and thus the DBus signal subscription alive.
    quit_event = asyncio.Event()
    connection = await Gio.bus_get(Gio.BusType.SESSION)  # type: ignore
    connection.signal_subscribe(  # type: ignore
        "org.freedesktop.portal.Desktop",
        "org.freedesktop.portal.Settings",
        "SettingChanged",
        "/org/freedesktop/portal/desktop",
        # Only listen to changes of appearance settings
        "org.freedesktop.appearance",
        Gio.DBusSignalFlags.MATCH_ARG0_NAMESPACE,  # type: ignore
        SettingChangedHandler(color_schemes),
    )  # type: ignore
    # Run until the handler quits
    await quit_event.wait()


def main() -> None:
    """Monitor the desktop color scheme and update Helix' color theme accordingly."""
    logging.basicConfig(level=logging.DEBUG)

    policy = GLibEventLoopPolicy()
    asyncio.set_event_loop_policy(policy)
    loop = cast(asyncio.EventLoop, policy.get_event_loop())

    apply_scheme_pool = ThreadPoolExecutor(
        max_workers=1, thread_name_prefix="apply-color-scheme-"
    )
    color_schemes: asyncio.Queue[ColorScheme] = asyncio.Queue()
    loop.create_task(process_color_scheme(apply_scheme_pool, color_schemes))
    loop.run_until_complete(monitor_changed_settings(color_schemes))


if __name__ == "__main__":
    try:
        main()
    except KeyboardInterrupt:
        pass
    finally:
        logging.shutdown()
