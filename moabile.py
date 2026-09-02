#!/usr/bin/env python3
"""MOABile — mother of all mobile.

Multi-device TUI for mobile app testing: Android over adb, jailbroken iOS
over usbmux and ssh.

Drives adb, scrcpy, libimobiledevice, iproxy, ioscpy, frida, objection, curl and
xz, which must already be on PATH; the startup screen reports what is missing
and which of the two device families that leaves usable. An iPhone is reached
with libimobiledevice for what needs no cooperation — info, syslog, installing
an ipa — and with ssh down an iproxy tunnel for a shell, the filesystem and
frida-server, authenticated with a password asked for once and kept in memory,
never a key left behind on the phone. Every attached device gets its own
panel with live stats, a log of everything run against it, and a pty for the
tool of the moment, and each panel keeps its own package and frida arguments —
so two devices can be worked in parallel without crossing over. Nothing is
written to disk between runs: what was selected, where the browser was and
which account reaches the phone are a record of the work, and this is a tool
for leaving none of that behind. Files move both ways through a browser
showing host and device side by side, and frida arguments are pointed at a
local script or a codeshare project by picking them off a list.

    python3 moabile.py
"""

from __future__ import annotations

import asyncio
import contextlib
import fcntl
import io
import os
import pty
import re
import shlex
import shutil
import signal
import socket
import struct
import subprocess
import sys
import tarfile
import tempfile
import termios
from html import unescape
from pathlib import Path
from typing import ClassVar, NamedTuple
from urllib.parse import quote

import pyte
from rich.errors import MarkupError
from rich.markup import escape
from rich.style import Style
from rich.text import Text
from textual import events, on, work
from textual.app import App, ComposeResult
from textual.binding import Binding, BindingType
from textual.containers import Horizontal, HorizontalScroll, Vertical
from textual.css.query import NoMatches
from textual.message import Message
from textual.notifications import SeverityLevel
from textual.screen import ModalScreen
from textual.theme import Theme
from textual.timer import Timer
from textual.widget import Widget
from textual.widgets import Footer, Header, Input, Label, ListItem, ListView, RichLog, Static

VERSION = "1.0.0"
# What --help says. There are no options to document: everything this does is
# chosen inside, with the keys. Printed rather than built with argparse, which
# would be a dependency's worth of machinery for a program that takes nothing.
USAGE = f"""moabile {VERSION} — mother of all mobile

A multi-device terminal UI for mobile app testing: android over adb, jailbroken
ios over usbmux and ssh, both at once, each attached device in its own panel.

    python3 moabile.py

No arguments and no options. What it does is chosen inside: the key bar at the
bottom of the screen holds the commands, and h opens the panel listing all of
them. adb, scrcpy, libimobiledevice, iproxy, ioscpy, frida, objection, curl and
xz have to be on PATH already — the startup screen says which are missing and
which device families that leaves usable.

  -h, --help       this
  -V, --version    the version and nothing else
"""

# The one directory adb can write to on a device with no root, which is where
# anything on its way somewhere else is staged.
ANDROID_TMP = "/data/local/tmp"
ANDROID_SERVER = f"{ANDROID_TMP}/frida-server"
ANDROID_FRIDA_SOCKET = f"{ANDROID_TMP}/re.frida.server"
ABIS = {"arm64-v8a": "arm64", "armeabi-v7a": "arm", "x86_64": "x86_64", "x86": "x86"}
# arm64e devices run the arm64 build: frida publishes no arm64e server.
IOS_ARCHS = {"arm64": "arm64", "arm64e": "arm64", "armv7": "arm", "armv7s": "arm"}
# Every real frida-server is tens of megabytes; anything smaller is a truncated
# download or an error page, and pushing it fails obscurely on the device.
MIN_SERVER_BYTES = 1_000_000
# A stream line longer than this is emitted as-is rather than buffered forever.
MAX_LINE_BYTES = 1_000_000
# adb runs this through `sh -c "<command>"`, so the shell's own command line
# contains the pattern and a plain `pgrep -f frida-server` always matches
# itself. The bracket keeps the literal out of the pattern's own text.
ANDROID_FRIDA_PS = "pgrep -f '[f]rida-server'"
# ps, not pgrep: a jailbroken phone has Darwin's ps, and pkill/pgrep are the
# half that is usually not installed. The whole table, and no grep either: that
# is not on every jailbreak, and one missing tool on the phone read as "nothing
# is running". Filtered on the host instead — frida-server by IosPanel.frida_re
# and the selected app by pid_of(), off the same output, where comm is the
# executable's full path, which is what iOS runs an app as.
IOS_PS = "ps -A -o pid,comm"
# What frida's iOS package carries, as it names the paths inside itself. The
# agent is not optional: frida-server loads it from beside itself and is inert
# without it. The /var/jb prefix is the package's own — a rootful jailbreak
# drops it.
IOS_FRIDA_FILES = ("/var/jb/usr/sbin/frida-server",
                   "/var/jb/usr/lib/frida-1.0/frida-agent.dylib")
# What the app list is asked for, in the order the tool prints them. The
# executable and the path are the two answers that otherwise cost a glob grep
# on the phone — seconds on a phone with a few hundred apps, and nothing at all
# on one with no grep, which is most of them. The command line before
# --attribute has three fixed columns instead, and no way to ask.
IOS_APP_ATTRS = ("CFBundleIdentifier", "CFBundleDisplayName", "CFBundleExecutable", "Path")
IOS_APP_COLUMNS = ("CFBundleIdentifier", "CFBundleVersion", "CFBundleDisplayName")
# What a non-interactive ssh does not put on the PATH. sysctl, vm_stat,
# ifconfig and ps are the phone's own, under /usr/sbin and /usr/bin; grep,
# open and everything else a jailbreak installs live under /var/jb on a
# rootless one. Without this the stats line read ? for the load, the memory
# and the address on every rootless device with nothing to say why — and
# worse, `grep` and `open` came back "not found", which the panel reported as
# a phone that has neither rather than as a PATH this end chose. It goes on
# every command IosPanel.run sends, and inside sudo as well as outside it:
# sudo replaces the PATH it is given with its own secure_path.
IOS_PATH = ("export PATH=$PATH:/usr/sbin:/usr/bin:/sbin:/bin"
            ":/var/jb/usr/sbin:/var/jb/usr/bin:/var/jb/sbin;")
# Status polls between one battery reading and the next. It is a fresh usbmux
# connection each time, for a number that does not move in three seconds.
BATTERY_TICKS = 10
# The first local port an iproxy tunnel is given; one per iOS panel upwards.
IOS_SSH_PORT = 2222
# How long to wait for iproxy to bind that port, in tenths of a second.
TUNNEL_TICKS = 30
# The account a jailbreak leaves reachable, and the password it ships with.
# root is often refused outright ("UNIX authentication refused") while mobile
# answers, and sudo covers the difference.
#
# "alpine" is not a credential and is not anybody's secret: it is the factory
# default OpenSSH password on every jailbroken iPhone, published as such in
# MASTG-TECH-0052 along with the hash it comes from. It is here so the common
# case needs no typing. A phone whose owner changed it — which that same page
# tells you to do — falls straight through to the prompt, and what is typed
# there stays in memory for as long as the panel is open and reaches no file.
IOS_DEFAULT_USER = "mobile"
IOS_DEFAULT_PASSWORD = "alpine"
# What a password prompt looks like, whichever way sshd asks — a fallback for
# when the terminal's own echo setting cannot be read back. It is not always
# the literal "password:": keyboard-interactive puts the account in the middle
# of it, as in "Password for mobile@some-iPhone:".
SSH_PROMPT = r"password[^\n]*:[ \t]*$"
# Tenths of a second to give ssh to authenticate and settle into a master.
SSH_MASTER_TICKS = 150
# Host key checking off and known_hosts nowhere: the far end is a tunnel to
# localhost whose key changes with the phone, so the only thing checking it
# would achieve is a warning nobody can act on.
SSH_LOUD_OPTS = ("-o", "StrictHostKeyChecking=no", "-o", "UserKnownHostsFile=/dev/null",
                 "-o", "ConnectTimeout=5")
# LogLevel=ERROR on top, for the commands whose output goes straight into the
# panel. Not for the one connection that authenticates: there it also swallowed
# the line saying why the phone hung up, which is how a refused login came back
# as "ssh exited without saying why". That one's output goes to a pty nobody
# watches and is shown only when it fails, so it has nothing to be quiet for.
SSH_OPTS = (*SSH_LOUD_OPTS, "-o", "LogLevel=ERROR")
# For the one connection that authenticates. The phone is reached with a
# password and deliberately nothing else, and offering keys is worse than
# pointless: ssh tries every key in ~/.ssh and in the agent first, sshd counts
# each one as a failed attempt, and a handful of them exhausts MaxAuthTries —
# six by default — before it ever asks for a password. That is what
# "Permission denied (publickey,keyboard-interactive)" means when no prompt
# was ever shown. One prompt, so a wrong password fails at once rather than
# spending two more of those tries.
SSH_PASSWORD_OPTS = ("-o", "PubkeyAuthentication=no",
                     "-o", "PreferredAuthentications=keyboard-interactive,password",
                     "-o", "NumberOfPasswordPrompts=1")
# frida-server is ~15 MB per version and architecture, and /tmp is emptied on
# reboot, so it is kept where a cache belongs and survives.
CACHE = Path(os.environ.get("XDG_CACHE_HOME") or Path.home() / ".cache") / "moabile"
CODESHARE = "https://codeshare.frida.re"
# Where every frida-server build comes from, whichever family asks for one.
FRIDA_RELEASES = "https://github.com/frida/frida/releases/download"
# Hits per page in the codeshare browser: two lines each, so this is what its
# list shows without scrolling.
CODESHARE_PAGE = 10
# Rows the app list draws at most. Every row is a widget mount: a hundred cost
# a fifth of a second and five hundred the best part of one, and that is paid
# again on every pause in the filter — so a phone carrying a couple of hundred
# apps froze the field it was being typed into. A dozen rows are visible at a
# time on an ordinary terminal, so this is a long way past what anybody
# scrolls: the rest is what the filter is for, and the head above the list
# says how many there are in all.
PACKAGE_ROWS = 200
# Both themes are this app's own, so the two look like one family and neither
# is at the mercy of what a Textual release does to its built-ins.
#
# The light one is not textual-light, which is white at full brightness with
# saturated accents — a sheet of paper aimed at your face on a terminal you
# have been reading all day. This is paper in a room with the lamp on: a warm
# grey ground rather than white, ink rather than black on top of it, and
# accents desaturated to where they read as colour without glowing.
DARK = Theme(
    name="moabile-dark",
    # Light enough to clear 4.5:1 against the lightest of the three grounds
    # below, the same rule the light theme is built to.
    primary="#5c9fbf",        # headings, borders, the accent on a modal
    secondary="#8499a6",
    accent="#c98a4b",
    foreground="#dcd7cf",
    background="#191a1b",
    surface="#212325",        # modals and the sidebar, a shade off the ground
    panel="#2b2e31",
    success="#6cae6c",
    warning="#d0a44a",
    error="#da7d71",
    dark=True,
)
LIGHT = Theme(
    name="moabile-light",
    # Every one of these is text on one of the three grounds below, so each is
    # dark enough to clear 4.5:1 against the darkest of them — a status colour
    # that reads as colour and not as a smudge is the whole reason the panel
    # uses them.
    primary="#22475a",
    secondary="#39454b",
    accent="#5e3c19",
    foreground="#26241f",     # ink, not #000: black on white is the glare
    background="#cfc9bb",     # the ground, well under the terminal's white
    surface="#c5bfb0",        # modals and the sidebar, a shade off the ground
    panel="#b8b1a0",
    success="#274b2d",
    warning="#553e0d",
    error="#742a21",
    dark=False,
)
# Under every empty-panel message: the key bar holds what the terminal is wide
# enough for, and this is the one key that lists the rest of them.
HELP_HINT = "\n\n[dim]h lists every key[/]"
# What the four keys that work on an app say when none is picked. One sentence
# in one place: four copies of it is four chances for three of them to drift.
NO_APP = "select an app in the sidebar first"
# Dark first: it is the default, and the light one is the only alternative.
KEEP_THEMES = (DARK.name, LIGHT.name)


# The mobile terminal frame with the MOAB bomb emblem and typography.
LOGO = r""".--------------------------------------------------.
| 12:00          (•)  [SYS: ARMED]    5G 100% [||] |
|==================================================|
|                                                  |
|                   _ . - - - . _                  |
|               . '  \  | : |  /  ' .              |
|             /   . - \\:___:// - .   \            |
|            |  /   *  \__*__/  *   \  |           |
|           [==|    --== MOAB ==--   |==]          |
|            |  \   *  /  *  \  *   /  |           |
|             \   ' - //:===:\\ - '   /            |
|               ' . _/  | : |  \_ . '              |
|                   )   | : |   (                  |
|                  (    | : |    )                 |
|                 /   .' ___ '.   \                |
|               /  . ' (_____) ' .  \              |
|             '======================='            |
|                                                  |
|       __  __   ___    _     ____  _ _            |
|      |  \/  | / _ \  / \   | __ )(_) | ___       |
|      | |\/| || | | |/ _ \  |  _ \| | |/ _ \      |
|      | |  | || |_| / ___ \ | |_) ) | |  __/      |
|      |_|  |_| \___/_/   \_\|____/|_|_|\___|      |
|                                                  |
|            >> mother of all mobile <<            |
|                                                  |
|==================================================|
|                      [ === ]                     |
'--------------------------------------------------'"""
# How long it stays before it takes itself off.
LOGO_SECONDS = 1.2
LOGO_ROWS = LOGO.count("\n") + 1
LOGO_COLS = max(len(line) for line in LOGO.splitlines())


def modal_css(name: str, max_width: int, max_height: int = 0) -> str:
    """The frame every modal in here wears: centred, a round accent border on
    the surface colour, and a share of the screen with a ceiling — so a narrow
    terminal still gets a popup rather than a full-screen page.

    Spelled out per class on purpose. Textual registers a screen's stylesheet
    scoped to the class being pushed, so a CSS attribute inherited from a base
    class styles nothing at all: that is how the frida argument screen used to
    open unstyled unless some other screen had been shown before it.
    """
    size = f"height: 86%; max-height: {max_height};" if max_height else "height: auto;"
    return (f"{name} {{ align: center middle; }}\n"
            f"{name} #box {{ width: 84%; max-width: {max_width}; {size}"
            f" border: round $accent; background: $surface; padding: 1 2; }}\n"
            f"{name} ListItem {{ background: transparent; color: $foreground; padding: 0 1; }}\n"
            f"{name} ListItem:hover {{ background: $panel; color: $foreground; }}\n"
            f"{name} ListItem.-highlight, {name} ListItem.-selected {{\n"
            f"    background: $panel; color: $foreground;\n}}\n"
            f"{name} ListView:focus > ListItem.-highlight,\n"
            f"{name} ListView:focus > ListItem.-selected {{\n"
            f"    background: $accent; color: $background;\n}}\n"
            f"{name} ListView:focus > ListItem.-highlight Label,\n"
            f"{name} ListView:focus > ListItem.-selected Label {{\n"
            f"    color: $background; text-style: bold;\n}}\n"
            f"{name} ListItem.-dir Label {{\n"
            f"    color: $primary; text-style: bold;\n}}\n"
            f"{name} ListView:focus > ListItem.-highlight.-dir Label,\n"
            f"{name} ListView:focus > ListItem.-selected.-dir Label {{\n"
            f"    color: $background; text-style: bold;\n}}\n")


class Tool(NamedTuple):
    name: str
    why: str        # what it is for, without naming the family: that has a column
    source: str     # the upstream project, when the binary name is not it already
    family: str = ""            # "" is needed whatever the device is
    flag: str = "--version"     # how this one is asked, where that is not it
    version: str = ""
    present: bool = False


# Grouped by what they drive: the core tools are needed either way, and each
# family is usable on its own — an Android-only machine has no reason to
# install libimobiledevice to get past the startup screen.
# No install commands here: which package manager the host has and what it
# calls a package both depend on the distribution and both drift. Each row
# names the upstream project instead, and only where that is not the binary
# name already.
DEPS = [
    Tool("frida", "instrumentation, and its version", "frida-tools"),
    # objection is a click program with subcommands and no --version option:
    # asked for one it answers "No such option" and exits 2.
    Tool("objection", "exploration REPL", "", flag="version"),
    Tool("curl", "fetch frida-server and codeshare", ""),
    Tool("xz", "unpack frida-server", "XZ Utils"),
    Tool("adb", "device control", "android platform-tools", "android"),
    Tool("scrcpy", "screen mirroring", "", "android"),
    Tool("idevice_id", "device discovery, info and syslog", "libimobiledevice", "ios"),
    Tool("ideviceinstaller", "ipa install and app list", "", "ios"),
    Tool("iproxy", "ssh tunnel over usb", "libusbmuxd", "ios"),
    Tool("ssh", "shell, filesystem and frida-server", "OpenSSH", "ios"),
    Tool("ioscpy", "screen mirroring", "github.com/lautarovculic/ioscpy", "ios"),
]


FAMILIES = ("android", "ios")


async def _nothing() -> tuple[int, str]:
    """Stand in for a command a missing toolchain means there is no point running."""
    return 0, ""


async def sh(*cmd: str, timeout: float = 15, feed: bytes = b"") -> tuple[int, str]:
    """Run a command, returning (exit code, combined output).

    Always with a deadline: a device that goes away mid-command leaves adb
    blocked forever, and with a status poll every few seconds those pile up
    until the interface stops responding. `feed` goes to its stdin, which is
    how sudo is given a password without it ever appearing in an argument
    list — anyone on the machine can read one of those out of `ps`.

    Nothing else gets a stdin at all. `ssh host cmd` and `adb shell cmd` both
    forward theirs to the far end, so a child inheriting this process's would
    be reading the keystrokes meant for the interface — and the status poll
    starts one every three seconds.
    """
    try:
        proc = await asyncio.create_subprocess_exec(
            *cmd, stdin=asyncio.subprocess.PIPE if feed else asyncio.subprocess.DEVNULL,
            stdout=asyncio.subprocess.PIPE, stderr=asyncio.subprocess.STDOUT,
            start_new_session=True,
        )
    except OSError as exc:                 # missing, not executable, no fork
        return 127, f"{cmd[0]}: {exc.strerror or exc}"
    try:
        out, _ = await asyncio.wait_for(proc.communicate(feed or None), timeout)
    except (asyncio.TimeoutError, TimeoutError):
        # The whole group: `sh -c "curl | xz -d"` leaves curl running otherwise.
        with contextlib.suppress(ProcessLookupError, OSError):
            os.killpg(os.getpgid(proc.pid), signal.SIGKILL)
        await proc.wait()
        return 124, f"{' '.join(cmd)}: timed out after {timeout:g}s"
    return proc.returncode or 0, out.decode(errors="replace")


_HELP: dict[tuple[str, str], bool] = {}


async def help_has(tool: str, needle: str) -> bool:
    """Whether a tool's own help mentions needle, asked once per tool.

    Every libimobiledevice CLI in here changed its arguments between releases,
    and guessing wrong fails as a usage dump or a refused connection with
    nothing saying why. Reading the help once is cheaper than either.
    """
    key = (tool, needle)
    if key not in _HELP:
        _, out = await sh(tool, "--help", timeout=5)
        _HELP[key] = needle in out
    return _HELP[key]


def port_free(port: int) -> bool:
    """Whether a local port can be bound right now.

    iproxy exits the moment its port is taken, so a tunnel left behind by a
    crash, or one started by hand, used to make the same dead port be retried
    every three seconds forever. No SO_REUSEADDR on purpose: a port still in
    TIME_WAIT reads as busy here, which costs one port number and is never
    wrong.
    """
    with socket.socket() as probe:
        try:
            probe.bind(("127.0.0.1", port))
        except OSError:
            return False
    return True


def port_listening(port: int) -> bool:
    """Whether something is already accepting connections on a local port.

    Asked by connecting, never by binding — which is the whole reason this is
    not `not port_free(port)`. The wait for iproxy to come up runs every tenth
    of a second on the very port iproxy is in the middle of binding, and a
    probe that binds it, even for the instant it takes to fail, takes it away
    from iproxy: that is how a tunnel of ours came back as "iproxy exited at
    once on port 2222", telling whoever was at the keyboard to go and unlock a
    phone that had nothing to do with it.

    A connect costs iproxy one channel it opens to the phone and finds empty,
    once per tunnel, and ssh opens a real one a moment later anyway.
    """
    with socket.socket() as probe:
        probe.settimeout(0.2)
        return probe.connect_ex(("127.0.0.1", port)) == 0


async def iproxy_argv(port: int, udid: str) -> list[str]:
    """iproxy's own argument order, which libusbmuxd 2.0 changed.

    Old: `iproxy LOCAL DEVICE [UDID]`. New: `iproxy LOCAL:DEVICE -u UDID`.
    """
    if await help_has("iproxy", "--udid"):
        return ["iproxy", f"{port}:22", "-u", udid]
    return ["iproxy", str(port), "22", udid]


async def installer_takes_commands() -> bool:
    """True where ideviceinstaller takes `install`/`list` rather than -i/-l."""
    return not await help_has("ideviceinstaller", "--install")


def ios_memory(lines: list[str]) -> str:
    """Used and total memory out of `sysctl -n hw.memsize` plus `vm_stat`.

    vm_stat counts pages and names the page size in its own header, which is
    16 KiB on every device this runs on and 4 KiB on the older ones — so the
    number is read, not assumed.
    """
    text = "\n".join(lines)
    total = next((int(tok) for tok in text.split() if tok.isdigit() and len(tok) > 8), 0)
    page = int(m.group(1)) if (m := re.search(r"page size of (\d+)", text)) else 4096
    free = sum(int(m) for m in re.findall(r"^Pages (?:free|inactive|speculative):\s+(\d+)",
                                          text, re.MULTILINE))
    if not total:
        return "?"
    used = max(0, total - free * page)
    return f"{used / 1e9:.1f}/{total / 1e9:.1f} GB"


def first(s: dict[str, list[str]], key: str, pattern: str = r"(.+)") -> str | None:
    """The first capture of pattern in a section of a batched command's output."""
    return next((m.group(1) for line in s.get(key, []) if (m := re.search(pattern, line))), None)


def mac_key(mac: str) -> str:
    """A MAC address in one shape, so two spellings of it compare equal.

    arp on macOS drops the leading zero of an octet — "a:bb:c:dd:ee:ff" — and
    lockdownd never does, so the two never matched as written. Padded rather
    than stripped: "a" and "aa" are different octets, and stripping made them
    the same string.
    """
    return ":".join((part.lstrip("0") or "0").rjust(2, "0")
                    for part in re.split(r"[:-]", mac.strip().lower()))


def short_serial(serial: str) -> str:
    """A serial cut to the sidebar's column, in the middle rather than the end.

    An iOS udid is forty characters and the column is fifteen — and the ends
    are what tells two of them apart, so the middle is what goes. Fifteen
    because the row around it is a mark, a space, two spaces and fourteen
    characters of the device's own name: thirty-three, which is the sidebar.

    Every place a serial is shortened uses this: the sidebar row, the panel
    border and the file browser's column heading. It was three different cuts,
    two of them off the front — which on a udid drops the only characters that
    tell one phone from the next. An android serial is short enough to come
    back whole.
    """
    return serial if len(serial) <= 15 else f"{serial[:10]}…{serial[-4:]}"


def is_package(ident: str) -> bool:
    """Whether what the device called an app is a name and not a path.

    Both families read the app list off the device, and both then put what
    they read into a path on this machine: e saves the apk or the ipa under
    it. A device is not ours to trust — an identifier carrying a slash, or a
    .., would land that file somewhere the directory picker never named — and
    no bundle id has either in it. The same reasoning as the codeshare slug,
    which is filtered where it is parsed because it ends up in an argument
    list. Nor can one open with a dash, for that same reason: an app named
    `-l` would reach frida as a flag. The dot is what the header row of the
    ios app list fails, and what every real identifier on both families has.
    """
    return bool(re.fullmatch(r"[A-Za-z0-9_][A-Za-z0-9_.-]*", ident)) \
        and "." in ident and ".." not in ident


def pid_of(lines: list[str], exe: str) -> str | None:
    """The pid running `exe`, out of `ps -o pid,comm` lines.

    The executable's own path and nothing shorter: an app called Target is not
    the TargetHelper beside it, and a name matched anywhere in the line found
    the pid of whatever had it as an argument.
    """
    if not exe:
        return None
    return next((m.group(1) for line in lines
                 if (m := re.match(rf"\s*(\d+)\s+\S*/{re.escape(exe)}$", line.rstrip()))),
                None)


def unpack_deb(deb: Path, into: Path) -> list[str]:
    """Unpack a .deb's payload under `into`, returning the paths it wrote.

    Written out rather than shelling out to dpkg-deb or bsdtar, neither of
    which is on every host: a .deb is an `ar` archive — a magic number and a
    table of fixed-width headers — whose payload member is a tar that the
    standard library already reads.

    Members are written by name rather than handed to extractall(): an archive
    off the internet does not get to choose where its files land, and the
    filter that says so is newer than the python this asks for.
    """
    blob = deb.read_bytes()
    if not blob.startswith(b"!<arch>\n"):
        raise ValueError(f"{deb.name}: not a deb")
    at = 8
    while at + 60 <= len(blob):
        name = blob[at:at + 16].decode(errors="replace").strip().rstrip("/")
        size = int(blob[at + 48:at + 58].decode(errors="replace").strip() or 0)
        at += 60
        if not name.startswith("data.tar"):
            at += size + size % 2
            continue
        written = []
        with tarfile.open(fileobj=io.BytesIO(blob[at:at + size])) as tar:
            for member in tar.getmembers():
                parts = [p for p in member.name.split("/") if p not in ("", ".")]
                if not member.isfile() or ".." in parts:
                    continue
                out = into.joinpath(*parts)
                out.parent.mkdir(parents=True, exist_ok=True)
                source = tar.extractfile(member)
                if source is None:
                    continue
                with out.open("wb") as sink:
                    shutil.copyfileobj(source, sink)
                written.append("/" + "/".join(parts))
        return written
    raise ValueError(f"{deb.name}: no data archive inside")


def last_line(text: str) -> str:
    """The last thing a command said, for reporting it in one line."""
    return text.strip().splitlines()[-1].strip() if text.strip() else ""


def not_there(out: str) -> bool:
    """Whether what a device said is "that command is not on me".

    A jailbreak ships half a userland and every shell words it differently —
    "sh: open: not found", "command not found", an exec answering "No such
    file or directory". None of it is a failure worth putting on screen: a
    tool the phone has not got is a fallback to take, not an error to report,
    and the shell's own wording tells whoever is at the keyboard nothing they
    can act on.
    """
    return bool(re.search(r"not found|No such file", out, re.IGNORECASE))


def echo_off(fd: int) -> bool:
    """Whether the far end of this pty has stopped echoing what is typed.

    Which is a program saying it is about to read a secret. A pty master can
    read back the settings the program put on its own end, so this is the one
    signal that does not depend on how the question happens to be worded.
    """
    with contextlib.suppress(OSError, ValueError):
        return not termios.tcgetattr(fd)[3] & termios.ECHO
    return False


def sections(out: str) -> dict[str, list[str]]:
    """Split the output of a batched shell command on its @marker lines."""
    result: dict[str, list[str]] = {}
    current: list[str] | None = None
    for line in out.splitlines():
        line = line.rstrip("\r")
        if line.startswith("@"):
            current = result.setdefault(line[1:], [])
        elif current is not None:
            current.append(line)
    return result


# pyte names colours the way DEC did; Rich does not know "brown" or "brightblue".
PYTE_COLORS = {
    "black": "black", "red": "red", "green": "green", "brown": "yellow",
    "blue": "blue", "magenta": "magenta", "cyan": "cyan", "white": "white",
    "brightblack": "bright_black", "brightred": "bright_red",
    "brightgreen": "bright_green", "brightbrown": "bright_yellow",
    "brightblue": "bright_blue", "brightmagenta": "bright_magenta",
    "brightcyan": "bright_cyan", "brightwhite": "bright_white",
}

# Textual key names -> the bytes a terminal would send.
KEYS = {
    "enter": b"\r", "tab": b"\t", "backspace": b"\x7f", "escape": b"\x1b",
    "up": b"\x1b[A", "down": b"\x1b[B", "right": b"\x1b[C", "left": b"\x1b[D",
    "home": b"\x1b[H", "end": b"\x1b[F", "delete": b"\x1b[3~",
    "pageup": b"\x1b[5~", "pagedown": b"\x1b[6~", "space": b" ",
    "shift+tab": b"\x1b[Z",
}


def pyte_color(name: str) -> str | None:
    if name == "default":
        return None
    return PYTE_COLORS.get(name) or (f"#{name}" if re.fullmatch(r"[0-9a-fA-F]{6}", name) else None)


class TerminalPane(Widget):
    """An interactive tool running on a real pty, drawn inside the panel.

    objection and the frida REPL are prompt_toolkit programs: they need a tty,
    they move the cursor and they repaint. Piping them into a log turns their
    output into garbage, and suspending the whole TUI to hand them the real
    terminal loses every other panel. A pty plus pyte gives them what they
    expect while the rest of the interface keeps running.
    """

    can_focus = True
    # Every key belongs to the child process — ctrl+c has to reach frida — so
    # the one way back out is a key no REPL uses and this pane never forwards.
    BINDINGS: ClassVar[list[BindingType]] = [
        Binding("f8", "leave", "leave the pane", show=False),
    ]

    def __init__(self, panel: DevicePanel) -> None:
        super().__init__(id=f"term-{panel.uid}")
        self.panel = panel
        self.proc: subprocess.Popen | None = None
        self.fd: int | None = None
        self.command: str = "tool"
        self.label: str = "tool"
        self.argv: list[str] = []
        # The spawn is deferred a frame, so `running` is still False in between;
        # without this a second keypress starts a second process and orphans the
        # first, whose pty nobody ever reads or closes.
        self.starting = False
        self.vt: pyte.Screen | None = None
        self.stream: pyte.ByteStream | None = None
        self._styles: dict[tuple, Style] = {}

    @property
    def running(self) -> bool:
        return self.proc is not None and self.proc.poll() is None

    def start(self, cmd: list[str], label: str = "") -> None:
        """Run cmd in the pane, showing label for it.

        The label is for when the real command line is machinery — the shell's
        PS1 setup, say, which nobody wants to read in a log or a title.
        """
        if self.running or self.starting:
            self.panel.write("[yellow]a tool is already running in this panel")
            return
        self.starting = True
        self.command, self.argv = cmd[0], list(cmd)
        self.label = label or shlex.join(cmd)
        # In the pane's own border: with frida and objection taking a dozen
        # arguments, "which one is this" is the question the pane has to
        # answer without being asked. Spaces around it: a partial border draws
        # the title flush against the rule, where a full box would not.
        self.border_title = f" {escape(self.label)} "
        # The pane has no height until the panel switches to the running layout,
        # and pyte's resize() wipes the screen — so spawn only once the layout
        # has settled, or the program's first output is erased under it.
        self.panel.set_class(True, "running")
        self.call_after_refresh(self._spawn, cmd)

    def _spawn(self, cmd: list[str]) -> None:
        # Stopped in the frame between start() and here — shutdown() does
        # exactly that on an unplug — so there is nothing to spawn any more,
        # and _teardown has already put the layout back.
        if not self.starting:
            return
        self.starting = False
        # is_attached, not is_mounted: a removed widget answers True to the
        # second one for as long as it exists, so it never caught the panel
        # closing under a spawn. See MOABile.keep_focus_alive.
        if not self.is_attached:               # panel closed before the layout settled
            self.panel.set_class(False, "running")
            return
        cols, rows = max(20, self.size.width or 80), max(5, self.size.height or 24)
        self.vt = pyte.Screen(cols, rows)
        self.stream = pyte.ByteStream(self.vt)
        try:
            # Its own controlling terminal: without one, job control and ctrl-c
            # never reach the program. See spawn_on_pty().
            self.proc, master = spawn_on_pty(
                cmd, env={**os.environ, "TERM": "xterm-256color"}, size=(rows, cols))
        except OSError as exc:
            self.panel.set_class(False, "running")
            self.panel.fail(f"{cmd[0]}: {exc}")
            return
        self.fd = master
        asyncio.get_running_loop().add_reader(master, self._readable)
        self.panel.write(f"[dim]$ {self.label}   (f8 leaves the pane)")
        self.focus()

    def stop(self) -> None:
        self.starting = False
        if self.running and self.proc:
            reap(self.proc)
            if self.proc.poll() is None:      # ignored the terminate: insist
                with contextlib.suppress(ProcessLookupError, OSError):
                    os.killpg(os.getpgid(self.proc.pid), signal.SIGKILL)
                with contextlib.suppress(subprocess.TimeoutExpired):
                    self.proc.wait(timeout=2)
        self._teardown()

    def _teardown(self) -> None:
        if self.fd is not None:
            with contextlib.suppress(RuntimeError, ValueError, OSError):
                asyncio.get_running_loop().remove_reader(self.fd)
            os.close(self.fd)
            self.fd = None
        # What the tool printed belongs to the tool's pane, not to the panel
        # log: dumping its last screen there mixed a frida session into the
        # record of what was run against the device. Only the exit is noted.
        if self.vt is not None:
            # The one place a tool's exit is reported: both ways out of a tool
            # come through here, and each used to write a line of its own.
            # Only a real exit code is worth naming — one we stopped ourselves
            # comes back as -15 for the SIGTERM, which is noise, not news.
            code = self.proc.poll() if self.proc else None
            name = escape(self.command)
            self.panel.write(f"[red]{name} exited with {code}" if code and code > 0
                             else f"[dim]{name} exited[/]")
        self.vt = self.stream = None
        self.panel.set_class(False, "running")
        if self.panel.is_attached:       # is_attached: see _spawn
            self.panel.focus()

    def _readable(self) -> None:
        try:
            data = os.read(self.fd, 65536) if self.fd is not None else b""
        except OSError:
            data = b""
        if not data:
            # poll(), not wait(): the pty can report EOF a moment before the
            # process is gone, and blocking here freezes the whole interface.
            if self.proc:
                self.proc.poll()
            self._teardown()
            return
        assert self.stream
        self.stream.feed(data)
        self.refresh()

    def action_leave(self) -> None:
        """Hand focus back to the panel; the tool keeps running."""
        self.panel.focus()

    def on_key(self, event: events.Key) -> None:
        # f8 first: this handler stops every key before bindings are looked at,
        # so the way out of the pane has to be let through here or it is eaten
        # along with the rest.
        if event.key == "f8" or not self.running or self.fd is None:
            return
        event.stop()
        event.prevent_default()
        data = KEYS.get(event.key)
        # a-z only: Textual names "ctrl+1" and "ctrl+@" the same shape, and the
        # arithmetic below goes negative there — bytes() raises, inside a key
        # handler, which takes the whole app down.
        if data is None and (m := re.fullmatch(r"ctrl\+([a-zA-Z])", event.key)):
            data = bytes([ord(m.group(1).lower()) - 96])
        if data is None and event.character:
            data = event.character.encode()
        if data:
            # EIO: the child can go between the poll() above and here, and an
            # exception out of a key handler takes the whole app with it.
            with contextlib.suppress(OSError):
                os.write(self.fd, data)

    def on_resize(self) -> None:
        if self.running and self.vt and self.fd is not None:
            cols, rows = max(20, self.size.width), max(5, self.size.height)
            if (rows, cols) == (self.vt.lines, self.vt.columns):
                return                       # pyte's resize() clears the screen
            self.vt.resize(rows, cols)
            _set_winsize(self.fd, rows, cols)
            with contextlib.suppress(ProcessLookupError):
                os.killpg(os.getpgid(self.proc.pid), signal.SIGWINCH)  # type: ignore[union-attr]

    def render(self) -> Text:
        if not self.vt:
            return Text("")
        cursor = self.vt.cursor
        out = Text()
        for y in range(self.vt.lines):
            row = self.vt.buffer[y]
            # Runs of identical style, so a full repaint is a few dozen spans
            # instead of one per character cell.
            run, style = "", None
            for x in range(self.vt.columns):
                char = row[x]
                key = (char.fg, char.bg, char.bold, char.italics, char.underscore,
                       char.reverse, not cursor.hidden and y == cursor.y and x == cursor.x)
                # Building a Style per cell per repaint dominated the cost of
                # drawing the pane; there are only a handful of distinct ones.
                if (here := self._styles.get(key)) is None:
                    here = self._styles[key] = Style(
                        color=pyte_color(char.bg if char.reverse else char.fg),
                        bgcolor=pyte_color(char.fg if char.reverse else char.bg),
                        bold=char.bold, italic=char.italics,
                        underline=char.underscore, reverse=key[-1],
                    )
                if here is not style:
                    out.append(run, style)
                    run, style = "", here
                run += char.data or " "
            out.append(run, style)
            if y != self.vt.lines - 1:
                out.append("\n")
        return out


def _set_winsize(fd: int, rows: int, cols: int) -> None:
    with contextlib.suppress(OSError):
        fcntl.ioctl(fd, termios.TIOCSWINSZ, struct.pack("HHHH", rows, cols, 0, 0))


def reap(proc: subprocess.Popen | None) -> None:
    """Stop a long-lived process this app started, and wait for it.

    The whole group, because half of these spawn a child that holds the work
    — scrcpy runs adb, and killing the parent alone leaves it — and every one
    of them is started in a session of its own, so the group is exactly that
    child and its own children. Waited for either way: a terminated child
    nobody waits on stays a zombie for as long as the app runs.

    SIGTERM and no escalation: the one place a program is given no choice is
    the tool pane, which insists with a SIGKILL of its own afterwards.
    """
    if not proc or proc.poll() is not None:
        return
    with contextlib.suppress(ProcessLookupError, OSError):
        os.killpg(os.getpgid(proc.pid), signal.SIGTERM)
    with contextlib.suppress(subprocess.TimeoutExpired):
        proc.wait(timeout=2)


def spawn_on_pty(argv: list[str], env: dict[str, str] | None = None,
                 size: tuple[int, int] | None = None) -> tuple[subprocess.Popen, int]:
    """Start a program on a pty of its own and hand back the near end.

    The child gets that pty as its *controlling* terminal, not merely as its
    stdin, and that distinction is the whole point of this function. ssh reads
    a password from /dev/tty and from nowhere else, and frida's REPL wants job
    control — and neither exists for a process that only has a terminal on fd
    0. `setsid` alone does not claim one: the ioctl does, and preexec_fn is
    the only place it can be made from. (A shell would paper over it by
    reopening the terminal itself, which is why this is easy to miss.)

    Returns (process, the pty's near end). Closing that end hangs up everyone
    attached to it, so hold it for as long as the child has to live.
    """
    primary, secondary = pty.openpty()
    if size:
        _set_winsize(primary, *size)

    def child() -> None:
        # Two syscalls, no allocation, and the second one is the one that
        # matters. See the docstring.
        os.setsid()
        fcntl.ioctl(0, termios.TIOCSCTTY, 0)

    try:
        proc = subprocess.Popen(
            argv, stdin=secondary, stdout=secondary, stderr=secondary,
            preexec_fn=child,  # noqa: PLW1509 — see child()
            env=env, close_fds=True)
    except OSError:
        os.close(primary)
        os.close(secondary)
        raise
    os.close(secondary)
    return proc, primary


class ValueItem(ListItem):
    """List row carrying its value; serials and package names are not valid ids."""

    def __init__(self, value: str, label: Text) -> None:
        # Text, not markup: serials and package names are not ours to trust.
        super().__init__(Label(label))
        self.value = value
        if value.endswith("/"):
            self.add_class("-dir")


class BarKey(Static):
    """A key pinned to one end of the bottom row.

    b and h open and close a panel instead of doing something to a device, and
    both are worth more where they cannot scroll away: seventeen keys share the
    bar between them and a narrow terminal shows only the front of it, which is
    exactly when h — the key that lists the ones cut off — has to still be
    there. Each sits on the side of what it opens: b at the left edge over the
    sidebar, h at the right.
    """

    def __init__(self, key: str, label: str, tooltip: str) -> None:
        # The footer's own colours, so a pinned key reads as part of the bar
        # rather than as a widget that happens to sit beside it.
        super().__init__(f"[$footer-key-foreground on $footer-key-background]{key}[/]"
                         f" [$footer-description-foreground]{label}[/]")
        self.key = key
        self.tooltip = tooltip

    def on_click(self) -> None:
        """Clickable, the way every key in the bar beside it is."""
        self.app.simulate_key(self.key)


class LogoScreen(ModalScreen[None]):
    """The name, once, on the way in. It leaves by itself; any key hurries it.

    A screen of its own because it cannot share one: even halved, the drawing
    is taller than the list of tools it would otherwise sit above. Shown only
    where there is room for it — a terminal too small gets the tool check
    straight away rather than a logo with its head cut off.
    """

    # The column is only as wide as the drawing, so centring the column
    # centres the drawing — and the name centres inside that same width
    # rather than inside its own handful of characters.
    CSS = ("LogoScreen { align: center middle; background: $surface; }\n"
           "LogoScreen Vertical { width: auto; height: auto; }\n"
           "LogoScreen .art { width: auto; color: $accent; }\n")

    def compose(self) -> ComposeResult:
        with Vertical():
            yield Static(LOGO, classes="art", markup=False)

    def on_mount(self) -> None:
        # Long enough to read, short enough that nobody has to dismiss it: this
        # is the screen in front of every single launch, and a keypress to get
        # past a logo is a toll.
        self.set_timer(LOGO_SECONDS, self.leave)

    def leave(self) -> None:
        # Only from the top of the stack: the timer can still fire after a key
        # has already taken it off.
        if self.is_active:
            self.dismiss(None)

    def on_key(self, event: events.Key) -> None:
        """Any key at all: this is a splash, not a question."""
        event.stop()
        self.leave()

    def on_mouse_down(self, event: events.MouseDown) -> None:
        event.stop()
        self.leave()


class DepsScreen(ModalScreen[str]):
    """Startup gate: the core tools, plus everything one device family needs.

    A machine with no libimobiledevice can still drive Android, and one with no
    adb can still drive an iPhone, so what blocks the way in is a missing core
    tool or neither family being complete — not every row having a tick.
    """

    BINDINGS: ClassVar[list[BindingType]] = [
        Binding("enter,space", "go", "continue"),
        Binding("r", "recheck", "recheck"),
        Binding("q,escape", "quit", "quit"),
    ]
    CSS = (modal_css("DepsScreen", 86, 40) + "DepsScreen .how { padding-left: 20; }\n"
           "DepsScreen #box { overflow-y: auto; }")

    def __init__(self, tools: list[Tool]) -> None:
        super().__init__()
        self.tools = tools
        self.missing = [t for t in tools if not t.present]
        self.ready = [f for f in FAMILIES if all(t.present for t in tools if t.family == f)]
        # A core tool missing, or no family complete: either way there is
        # nothing this app could usefully do past this screen.
        self.blocked = any(not t.family for t in self.missing) or not self.ready

    def compose(self) -> ComposeResult:
        with Vertical(id="box"):
            yield Static("[b]MOABile[/]  [dim]mother of all mobile[/]"
                         "  ·  [b]tool check[/]\n")
            for tool in self.tools:
                mark = "[$success]✓[/]" if tool.present else "[$error]✗[/]"
                shown = tool.version if tool.present else "missing"
                # Padded on the visible text, not the markup: the tags in
                # "[$error]missing[/]" are not columns on the screen.
                state = escape(shown) if tool.present else "[$error]missing[/]"
                pad = " " * max(1, 13 - len(shown))
                family = f"[dim]{tool.family}[/] " if tool.family else ""
                yield Static(f"{mark} [b]{tool.name:<17}[/] {state}{pad}{family}"
                             f"[dim]{tool.why}[/]")
                if not tool.present and tool.source:
                    # The class carries the indent, so a hint that wraps stays
                    # in its column instead of starting again at the border.
                    yield Static(f"[dim]from {tool.source}[/]", classes="how")
            if self.blocked:
                names = ", ".join(t.name for t in self.missing)
                yield Static(f"\n[$error]install {names} first.[/]  [dim]r recheck · q quit[/]")
            else:
                # Which families this leaves usable, because the missing rows
                # above stay red and would otherwise read as a broken app.
                short = [t.name for t in self.missing]
                gone = f"  [dim](no {', '.join(short)}: " + \
                       f"{', '.join(f for f in FAMILIES if f not in self.ready)} is out)[/]" \
                       if short else ""
                yield Static(f"\n[dim]enter continue · r recheck · q quit[/]"
                             f"  [$success]{' and '.join(self.ready)}[/]{gone}")

    def action_go(self) -> None:
        # No way past this screen while nothing here can drive a device: half
        # the bindings would fail later with an error that says nothing useful.
        self.dismiss("recheck" if self.blocked else "go")

    def action_recheck(self) -> None:
        self.dismiss("recheck")

    def action_quit(self) -> None:
        self.dismiss("quit")


class AskScreen(ModalScreen[str | None]):
    """One line of text, prefilled with whatever it was before."""

    BINDINGS: ClassVar[list[BindingType]] = [Binding("escape", "cancel", "cancel")]
    CSS = modal_css("AskScreen", 92)
    HINT = "[dim]enter accept · esc cancel[/]"

    def __init__(self, title: str, value: str, hint: str = "", secret: bool = False) -> None:
        super().__init__()
        self.title_text, self.value, self.hint = title, value, hint
        # A password is the one thing asked for here that must not be on
        # screen: panels are shared, and screenshots are one key away.
        self.secret = secret

    def compose(self) -> ComposeResult:
        with Vertical(id="box"):
            yield Static(f"[b]{escape(self.title_text)}[/]")
            if self.hint:
                yield Static(f"[dim]{escape(self.hint)}[/]")
            yield Input(value=self.value, id="answer", password=self.secret)
            yield Static(self.HINT)

    def on_mount(self) -> None:
        # NoMatches: a modal can be pushed and taken off again before its own
        # children are mounted, and an exception here takes the whole app down.
        with contextlib.suppress(NoMatches):
            self.query_one("#answer", Input).focus()

    @on(Input.Submitted)
    def submitted(self, event: Input.Submitted) -> None:
        self.dismiss(event.value)

    def action_cancel(self) -> None:
        self.dismiss(None)


class FridaArgsScreen(AskScreen):
    """The frida argument line, with the two arguments nobody wants to type.

    ctrl+o browses the disk for a script, ctrl+g browses codeshare, and either
    one appends its flag to what is already there.
    """

    CSS = modal_css("FridaArgsScreen", 92)
    BINDINGS: ClassVar[list[BindingType]] = [
        Binding("ctrl+o", "pick_local", "open script"),
        Binding("ctrl+g", "pick_codeshare", "get from codeshare"),
    ]
    HINT = "[dim]enter run · ctrl+o open script · ctrl+g get from codeshare · esc cancel[/]"

    def __init__(self, title: str, value: str, hint: str = "", local_dir: str = ".") -> None:
        super().__init__(title, value, hint)  # never secret: these are arguments
        # Where the script browser opens, and where it was left: the caller
        # reads it back off the screen to remember it for next time.
        self.local_dir = local_dir

    def add(self, token: str) -> None:
        """Append an argument, leaving the cursor after it."""
        answer = self.query_one("#answer", Input)
        answer.value = f"{answer.value.strip()} {token}".strip()
        answer.action_end()
        answer.focus()

    @work
    async def action_pick_local(self) -> None:
        if path := await self.app.push_screen_wait(ScriptScreen(self.local_dir)):
            self.local_dir = str(Path(path).parent)
            self.add(f"-l {shlex.quote(path)}")

    @work
    async def action_pick_codeshare(self) -> None:
        if slug := await self.app.push_screen_wait(CodeshareScreen()):
            self.add(f"--codeshare {slug}")


class ConfirmScreen(ModalScreen[bool]):
    """A yes/no question. Enter and escape both take the answer that changes
    nothing, so leaning on the keyboard never overwrites anything."""

    BINDINGS: ClassVar[list[BindingType]] = [
        Binding("y", "yes", "yes"),
        Binding("n,escape,enter", "no", "no"),
    ]
    CSS = modal_css("ConfirmScreen", 92)

    def __init__(self, question: str, yes: str, no: str) -> None:
        super().__init__()
        self.question, self.yes, self.no = question, yes, no

    def compose(self) -> ComposeResult:
        with Vertical(id="box"):
            yield Static(f"[b]{escape(self.question)}[/]\n")
            yield Static(f"[b]y[/]  {escape(self.yes)}")
            yield Static(f"[b]n[/]  {escape(self.no)}   [dim](enter, esc)[/]")

    def action_yes(self) -> None:
        self.dismiss(True)

    def action_no(self) -> None:
        self.dismiss(False)


class FileList(Vertical):
    """One filesystem in one column: what it is, where we are, what is here.

    Two of these side by side are the file browser — the host adb runs on and
    the device — and only the listing differs, so that is all a subclass gives.
    """

    DEFAULT_CSS = """
    FileList { width: 1fr; padding: 0 1; }
    FileList > Input { border: none; background: $panel; }
    FileList > ListView { height: 1fr; max-height: 100%; background: transparent; }
    FileList > ListView > ListItem { background: transparent; color: $foreground; padding: 0 1; }
    FileList > ListView > ListItem:hover { background: $panel; color: $foreground; }
    FileList > ListView > ListItem.-highlight,
    FileList > ListView > ListItem.-selected { background: $panel; color: $foreground; }
    FileList > ListView:focus > ListItem.-highlight,
    FileList > ListView:focus > ListItem.-selected { background: $accent; color: $background; }
    FileList > ListView:focus > ListItem.-highlight Label,
    FileList > ListView:focus > ListItem.-selected Label {
        color: $background; text-style: bold;
    }
    FileList > ListView > ListItem.-dir Label { color: $primary; text-style: bold; }
    FileList > ListView:focus > ListItem.-highlight.-dir Label,
    FileList > ListView:focus > ListItem.-selected.-dir Label {
        color: $background; text-style: bold;
    }
    """

    class Chose(Message):
        """Enter on a file, not a directory."""

        def __init__(self, side: FileList, path: str) -> None:
            super().__init__()
            self.side, self.path = side, path

    class Moved(Message):
        """The column is showing a different directory."""

    def __init__(self, path: str) -> None:
        super().__init__()
        self.path = path

    def compose(self) -> ComposeResult:
        yield Static(self.title())
        yield Input(value=self.path, placeholder="type a path, enter to go")
        yield ListView()

    def on_mount(self) -> None:
        self.reload()

    def title(self) -> str:
        raise NotImplementedError

    async def listing(self) -> tuple[int, str]:
        """(exit code, one name per line, directories suffixed with "/")."""
        raise NotImplementedError

    async def delete(self, path: str) -> tuple[int, str]:
        """Delete one file. (exit code, what to report).

        Files only, on both sides: a directory here would take whatever is
        inside it with no way to look first — see FilesScreen.file_at_cursor,
        which is what stops the key, and the `rm` and `unlink` below, which
        refuse one even if it ever got past.

        Not `remove`: a FileList is a Widget, and Widget.remove() already
        means "take this off the screen" — one Textual call away from
        deleting the wrong thing entirely.
        """
        raise NotImplementedError

    async def rename(self, path: str, name: str) -> tuple[int, str]:
        """Rename within the same directory. (exit code, what to report)."""
        raise NotImplementedError

    async def exists(self, name: str) -> bool:
        """Whether a child name exists in this directory."""
        raise NotImplementedError

    def child(self, name: str) -> str:
        return f"{self.path.rstrip('/')}/{name.rstrip('/')}"

    def go(self, path: str) -> None:
        self.path = path
        self.query_one(Input).value = path
        self.reload()

    def up(self) -> None:
        self.go(self.path.rstrip("/").rpartition("/")[0] or "/")

    def highlighted(self) -> str | None:
        """The entry under the cursor, as listed — a directory keeps its "/"."""
        item = self.query_one(ListView).highlighted_child
        return item.value if isinstance(item, ValueItem) and item.value else None

    @work(group="listing", exclusive=True)
    async def reload(self) -> None:
        self.post_message(self.Moved())
        rc, out = await self.listing()
        # NoMatches: the screen can be dismissed while a listing is in flight.
        with contextlib.suppress(NoMatches):
            self.query_one(Static).update(self.title())
            lv = self.query_one(ListView)
            lv.clear()
            # A name and nothing else: `ls` on the device is what answered
            # here, and a device is not ours to trust. An entry carrying a
            # slash — or a .. — is a path, and enter, d and n would then work
            # on something the column never showed.
            listed = [n for ln in out.splitlines() if (n := ln.strip())
                      and "/" not in n.rstrip("/") and n.rstrip("/") not in (".", "..")]
            # Directories first, then files: a phone directory has hundreds of
            # entries and the ones worth descending into are what you came for.
            names = sorted(listed, key=lambda n: (not n.endswith("/"), n.lower()))
            if rc != 0 or not names:
                lv.append(ValueItem("", Text(out.strip() or "empty", "red" if rc else "dim")))
                return
            for name in names:
                lv.append(ValueItem(name, Text(name, "bold" if name.endswith("/") else "")))
            # A list with no cursor is a list where the next key does nothing:
            # clear() drops the index, and a reload happens after every copy,
            # rename and delete.
            lv.index = 0

    @on(ListView.Selected)
    def entry_selected(self, event: ListView.Selected) -> None:
        event.stop()
        if not (isinstance(item := event.item, ValueItem) and item.value):
            return
        if item.value.endswith("/"):
            self.go(self.child(item.value))
        else:
            self.post_message(self.Chose(self, self.child(item.value)))

    @on(Input.Submitted)
    def path_typed(self, event: Input.Submitted) -> None:
        event.stop()
        self.go(event.value.strip() or "/")
        self.query_one(ListView).focus()


class HostList(FileList):
    """The machine adb itself runs on."""

    def __init__(self, path: str, suffix: str = "") -> None:
        super().__init__(path)
        self.suffix = suffix               # list only files ending in this

    def title(self) -> str:
        only = f"  [dim]{escape(self.suffix)} only[/]" if self.suffix else ""
        return f"[b]host[/]{only}"

    async def listing(self) -> tuple[int, str]:
        try:
            # As a context manager: an entry that raises part way through
            # otherwise leaves the directory handle open until a collection.
            with os.scandir(self.path) as entries:
                names = [f"{e.name}/" if e.is_dir() else e.name for e in entries
                         if e.is_dir() or e.name.endswith(self.suffix)]
        except OSError as exc:             # gone, or not ours to read
            return 1, str(exc)
        return 0, "\n".join(names)

    async def delete(self, path: str) -> tuple[int, str]:
        try:
            # unlink, never rmtree: a directory raises here, which is the point.
            Path(path).unlink()
        except OSError as exc:
            return 1, str(exc)
        return 0, f"removed {path}"

    async def rename(self, path: str, name: str) -> tuple[int, str]:
        try:
            Path(path).rename(Path(path).with_name(name))
        except (OSError, ValueError) as exc:      # ValueError: nothing to rename
            return 1, str(exc)
        return 0, f"{path} -> {name}"

    async def exists(self, name: str) -> bool:
        return (Path(self.path) / name.rstrip("/")).exists()


class DeviceList(FileList):
    """The device, over whatever reaches it — adb with su, or ssh as root.

    The panel owns that difference, so this column is the same listing either
    way: `ls -pA` is understood by toybox, busybox and Darwin alike.
    """

    def __init__(self, panel: DevicePanel) -> None:
        super().__init__(panel.remote_dir)
        self.panel = panel

    def title(self) -> str:
        return (f"[b]{self.panel.kind}[/]  {escape(short_serial(self.panel.serial))}"
                f"{'  [$success]root[/]' if self.panel.root else '  [$error]no root[/]'}")

    async def listing(self) -> tuple[int, str]:
        return await self.panel.run(f"ls -pA {shlex.quote(self.path)}")

    async def delete(self, path: str) -> tuple[int, str]:
        rc, out = await self.panel.run(f"rm -f {shlex.quote(path)}")
        return rc, out.strip() or f"removed {path}"

    async def rename(self, path: str, name: str) -> tuple[int, str]:
        dest = f"{path.rstrip('/').rpartition('/')[0]}/{name}"
        rc, out = await self.panel.run(f"mv {shlex.quote(path)} {shlex.quote(dest)}")
        return rc, out.strip() or f"{path} -> {name}"

    async def exists(self, name: str) -> bool:
        dest = f"{self.path.rstrip('/')}/{name.rstrip('/')}"
        rc, _ = await self.panel.run(f"test -e {shlex.quote(dest)}")
        return rc == 0


class FilesScreen(ModalScreen[None]):
    """Both filesystems at once: the host on the left, the device on the right.

    adb push and pull already copy whole directories; what they cannot do is
    show what is on either end, which is what this is for. Enter on a file
    sends it to the other side, so which way it goes is never a guess.
    """

    BINDINGS: ClassVar[list[BindingType]] = [
        Binding("escape,q", "close", "close"),
        # Every key here is the letter its own word is read by, as in the main
        # bar: p push, l pull, d delete, n rename, a app data, h home, r reload.
        # It was u for push and p for pull, where the p everybody reached for
        # was the one that copied the other way.
        Binding("p", "push", "push"),
        Binding("l", "pull", "pull"),
        Binding("n", "rename", "rename"),
        Binding("d", "delete", "delete"),
        Binding("a", "app_dir", "app data"),
        Binding("h", "home_dir", "home"),
        Binding("left", "focus_host", "host side"),
        Binding("right", "focus_device", "device side"),
        Binding("backspace", "up", "up"),
        Binding("r", "reload", "reload"),
    ]
    CSS = modal_css("FilesScreen", 132, 40) + """
    FilesScreen #sides { height: 1fr; }
    FilesScreen HostList { border-right: solid $panel; }
    """
    HINT = ("[dim]enter open, or send a file to the other side · p push · l pull"
            " · a app data · h home · n rename · d delete (files only)"
            " · ←/→ switch side · backspace up · r reload · esc close[/]")

    def __init__(self, panel: DevicePanel) -> None:
        super().__init__()
        self.panel = panel
        self.host = HostList(panel.local_dir)
        self.device = DeviceList(panel)

    def compose(self) -> ComposeResult:
        with Vertical(id="box"):
            yield Static(id="where")
            with Horizontal(id="sides"):
                yield self.host
                yield self.device
            yield Static(self.HINT)

    def on_mount(self) -> None:
        self.device.query_one(ListView).focus()

    @on(FileList.Moved)
    def moved(self) -> None:
        """Both directions, with the two directories in them.

        The keys alone never made it obvious which end was the device.
        """
        self.query_one("#where", Static).update(
            f"[b]pull[/] {self.panel.kind} {escape(self.device.path)}"
            f" [b]→[/] host {escape(self.host.path)}\n"
            f"[b]push[/] host {escape(self.host.path)}"
            f" [b]→[/] {self.panel.kind} {escape(self.device.path)}"
        )

    @on(FileList.Chose)
    def chose(self, event: FileList.Chose) -> None:
        self.transfer("pull" if event.side is self.device else "push", event.path)

    def focused_side(self) -> FileList | None:
        node: object = self.focused
        while node is not None:
            if isinstance(node, FileList):
                return node
            node = getattr(node, "parent", None)
        return None

    def action_focus_host(self) -> None:
        self.host.query_one(ListView).focus()

    def action_focus_device(self) -> None:
        self.device.query_one(ListView).focus()

    def action_up(self) -> None:
        if side := self.focused_side():
            side.up()

    def action_reload(self) -> None:
        self.host.reload()
        self.device.reload()

    def action_push(self) -> None:
        # Whatever the cursor is on, or the directory itself: adb copies both.
        picked = self.host.highlighted()
        self.transfer("push", self.host.child(picked) if picked else self.host.path)

    def action_pull(self) -> None:
        picked = self.device.highlighted()
        self.transfer("pull", self.device.child(picked) if picked else self.device.path)

    @work(group="edit")
    async def action_app_dir(self) -> None:
        """Point the device column at the selected app's own data directory.

        The one directory anybody opening this is looking for, and the one
        hardest to reach by hand: on iOS it is named after a uuid that matches
        nothing you know, and on android it sits behind root.
        """
        if not self.panel.package:
            self.notify(NO_APP, severity="warning")
            return
        if where := await self.panel.data_dir():
            self.device.go(where)
        else:
            self.notify(f"{self.panel.package}: no data directory found on the device",
                        severity="warning")

    def action_home_dir(self) -> None:
        """Point the device column back where it opened: /sdcard, or /var/mobile.

        The way out of the app's own directory, and out of wherever else
        backspace and enter ended up — both of which are several levels from
        anything, and neither of which the device side has a path bar habit
        for. Not the host's business: that column starts where the shell was.
        """
        self.device.go(self.panel.home_dir)

    def action_close(self) -> None:
        self.panel.local_dir, self.panel.remote_dir = self.host.path, self.device.path
        self.dismiss(None)

    @work(group="transfer")
    async def transfer(self, direction: str, target: str) -> None:
        into = self.device.path if direction == "push" else self.host.path
        item = target.rstrip("/").rsplit("/", 1)[-1]
        dest_side = self.device if direction == "push" else self.host
        dest_name = self.side_name(dest_side)
        if await dest_side.exists(item):
            if not await self.app.push_screen_wait(ConfirmScreen(
                f"overwrite {item} on {dest_name}?", "overwrite", "cancel",
            )):
                self.panel.write(
                    f"[dim]{direction} cancelled — existing {item} on {dest_name} not overwritten"
                )
                return
        else:
            if not await self.app.push_screen_wait(ConfirmScreen(
                f"{direction} {target}",
                f"copy it to {dest_name} {into}",
                "cancel",
            )):
                return
        rc, out = await (self.panel.push(target, into) if direction == "push"
                         else self.panel.pull(target, into))
        self.report(rc, out)
        # Whichever side received the file now shows it.
        dest_side.reload()

    def side_name(self, side: FileList) -> str:
        """Which of the two filesystems a path is on, for a question about it."""
        return "host" if side is self.host else self.panel.kind

    def file_at_cursor(self) -> tuple[FileList, str] | None:
        """The side in focus and the file it is pointing at, or a complaint.

        Files only. Deleting or renaming a directory here would take whatever
        is inside it with no way to look first, and a mistyped keystroke is
        not worth a subtree.
        """
        if not (side := self.focused_side()) or not (name := side.highlighted()):
            self.notify("nothing under the cursor", severity="warning")
            return None
        if name.endswith("/"):
            self.notify("directories are left alone — this works on files", severity="warning")
            return None
        return side, side.child(name)

    @work(group="edit")
    async def action_delete(self) -> None:
        """Delete the file the cursor is on, on whichever side has focus."""
        if not (found := self.file_at_cursor()):
            return
        side, target = found
        if not await self.app.push_screen_wait(ConfirmScreen(
                f"delete {target}", f"delete it from {self.side_name(side)}",
                "leave it alone")):
            return
        rc, out = await side.delete(target)
        self.report(rc, out)
        side.reload()

    @work(group="edit")
    async def action_rename(self) -> None:
        """Rename the file the cursor is on, in the directory it is already in."""
        if not (found := self.file_at_cursor()):
            return
        side, target = found
        was = target.rsplit("/", 1)[-1]
        name = await self.app.push_screen_wait(AskScreen(
            f"rename {target}", was,
            f"the new name, in the same directory on {self.side_name(side)}"))
        if not (name := (name or "").strip()) or name == was:
            return
        # A name, never a path. Path.rename refuses one on the host side by
        # raising; `mv` on the device would have taken it and moved the file
        # somewhere else entirely, which is not what the question asked.
        if "/" in name:
            self.notify("a name, not a path: this renames in place", severity="warning")
            return
        if await side.exists(name) and not await self.app.push_screen_wait(ConfirmScreen(
            f"overwrite {name} on {self.side_name(side)}?", "overwrite", "cancel",
        )):
            self.panel.write(
                f"[dim]rename cancelled — existing {name} on {self.side_name(side)} not overwritten"
            )
            return
        rc, out = await side.rename(target, name)
        self.report(rc, out)
        side.reload()

    def report(self, rc: int, out: str) -> None:
        if rc == 0:
            self.panel.write(escape(out))
        else:
            self.panel.fail(out)


class ScriptScreen(ModalScreen[str | None]):
    """Pick one file off the host — a `frida -l` script, an apk to install.

    Directories and files ending in `suffix` only: the rest of a source tree is
    noise when what you are after is a hook script or an apk. With `pick_dir`
    the answer is a directory instead, which is how a destination is chosen —
    the files listed there are context, and enter on one is not an answer.
    """

    BINDINGS: ClassVar[list[BindingType]] = [
        Binding("escape,q", "close", "cancel"),
        Binding("backspace", "up", "up"),
        Binding("r", "reload", "reload"),
        Binding("s", "here", "save here"),
    ]
    CSS = modal_css("ScriptScreen", 96, 32)

    def __init__(self, path: str, suffix: str = ".js", pick_dir: bool = False) -> None:
        super().__init__()
        self.side = HostList(path, suffix)
        self.pick_dir = pick_dir

    def compose(self) -> ComposeResult:
        with Vertical(id="box"):
            yield self.side
            what = "s save here · " if self.pick_dir else ""
            yield Static(f"[dim]enter open{'' if self.pick_dir else '/pick'} · backspace up"
                         f" · {what}r reload · esc cancel[/]")

    def on_mount(self) -> None:
        self.side.query_one(ListView).focus()

    @on(FileList.Chose)
    def chose(self, event: FileList.Chose) -> None:
        # Taking a file as the destination would overwrite that file.
        if self.pick_dir:
            self.notify("s saves into the directory on screen", severity="warning")
            return
        self.dismiss(event.path)

    def check_action(self, action: str, _parameters: tuple[object, ...]) -> bool:
        # s only means something when a directory is the answer; otherwise the
        # key is listed in the help panel and does nothing when pressed.
        return self.pick_dir if action == "here" else True

    def action_here(self) -> None:
        self.dismiss(self.side.path)

    def action_up(self) -> None:
        self.side.up()

    def action_reload(self) -> None:
        self.side.reload()

    def action_close(self) -> None:
        self.dismiss(None)


class Script(NamedTuple):
    slug: str        # owner/project, which is what --codeshare takes
    title: str
    likes: str
    about: str


def parse_codeshare(page: str) -> tuple[list[Script], int]:
    """Scripts listed on one codeshare page, and how many pages the pager has.

    Split per <article> first: a single regex over the whole page lets one
    entry missing a field swallow the next entry's.
    """
    scripts = []
    for block in page.split("<article>")[1:]:
        # The slug comes from the URL, never from the heading: the display
        # title has spaces and capitals, and --codeshare would not find it.
        # Word characters, dots and dashes only — this is a page off the
        # internet, and the slug goes into an argument list: anything with a
        # space in it would arrive at frida as two arguments, of which the
        # second was never ours.
        if not (m := re.search(r'href="[^"]*?/@([\w.-]+)/([\w.-]+)/?"', block)):
            continue
        title = re.search(r"<h2>.*?>([^<]*)</a>", block, re.DOTALL)
        likes = re.search(r"thumbs-o-up[^>]*></i>\s*([^<|]+)", block)
        about = re.search(r"<p>(.*?)</p>", block, re.DOTALL)
        scripts.append(Script(
            f"{m.group(1)}/{m.group(2)}",
            unescape(title.group(1)).strip() if title else m.group(2),
            likes.group(1).strip() if likes else "?",
            " ".join(unescape(about.group(1)).split()) if about else "",
        ))
    pages = max((int(n) for n in re.findall(r"\?page=(\d+)", page)), default=1)
    return scripts, pages


class CodeshareScreen(ModalScreen[str | None]):
    """Browse and search codeshare.frida.re, returning an owner/project slug.

    Browsing is paged by the site itself (?page=N). Search is not: it answers
    with every hit in one response — hundreds of them for a word like "root" —
    so those are cut into pages here and the response is kept, not refetched.
    """

    BINDINGS: ClassVar[list[BindingType]] = [
        # The plain letters reach here only when the list has focus — the
        # search box swallows them — which is how the file browsers work too.
        Binding("escape,q", "close", "cancel"),
        Binding("right,ctrl+n", "next", "next page"),
        Binding("left,ctrl+b", "prev", "back a page"),
        Binding("r,ctrl+r", "reload", "reload"),
    ]
    CSS = modal_css("CodeshareScreen", 110, 34) + """
    CodeshareScreen ListView { height: 1fr; max-height: 100%; }
    """

    def __init__(self, needle: str = "") -> None:
        super().__init__()
        self.needle = needle
        self.page = 1
        self.pages = 1
        self.found: list[Script] = []
        self.found_for: str | None = None

    def compose(self) -> ComposeResult:
        with Vertical(id="box"):
            yield Static(id="where")
            yield Input(value=self.needle, placeholder="search codeshare…", id="needle")
            yield ListView(id="hits")
            yield Static("[dim]enter pick · type + enter search · → next page · ← back"
                         " · r reload · esc cancel[/]")

    def on_mount(self) -> None:
        self.query_one("#hits", ListView).focus()
        self.load()

    @on(Input.Submitted, "#needle")
    def search(self, event: Input.Submitted) -> None:
        self.needle, self.page = event.value.strip(), 1
        self.query_one("#hits", ListView).focus()
        self.load()

    @work(group="codeshare", exclusive=True)
    async def load(self) -> None:
        if (scripts := await self.fetch()) is None:
            return
        if self.needle:
            # Ceiling division without importing math for one line.
            self.pages = max(1, -(-len(scripts) // CODESHARE_PAGE))
            self.page = min(self.page, self.pages)
        window = (scripts[(self.page - 1) * CODESHARE_PAGE:self.page * CODESHARE_PAGE]
                  if self.needle else scripts)
        self.query_one("#where", Static).update(
            f"[b]{escape(self.label())}[/]  ·  page {self.page}/{self.pages}"
            f"  ·  {len(scripts)} scripts"
        )
        lv = self.query_one("#hits", ListView)
        lv.clear()
        for s in window or [Script("", "nothing here", "", "")]:
            # Two lines each, the way the tool check and the help panel read:
            # the slug is what you are choosing, the description is why. All of
            # it assembled as Text, never markup, so a description written by
            # a stranger cannot break the list.
            lv.append(ValueItem(s.slug, Text.assemble(
                (s.slug or s.title, "bold"), (f"  ♥{s.likes}" if s.likes else ""),
                ("\n  " + s.about[:150], "dim") if s.about else "",
            )))

    async def fetch(self) -> list[Script] | None:
        """Scripts for the current query and page, or None if the fetch failed.

        A search answers with every hit at once, so it is kept and paged from
        memory; only a new query, or ctrl+r, goes back to the site. An empty
        list is a real answer — codeshare says "no results" with a page that
        parses to nothing — and is drawn as such rather than as an error.
        """
        if self.needle and self.found_for == self.needle:
            return self.found
        where = self.query_one("#where", Static)
        where.update(f"[dim]fetching {escape(self.label())}…[/]")
        url = (f"{CODESHARE}/search/?query={quote(self.needle)}" if self.needle
               else f"{CODESHARE}/browse?page={self.page}")
        # curl, not urllib: it is already a dependency, it honours the proxy
        # environment, and sh() gives it a deadline and kills it on timeout.
        rc, out = await sh("curl", "-fsSL", url, timeout=30)
        if rc != 0:
            lv = self.query_one("#hits", ListView)
            lv.clear()
            lv.append(ValueItem("", Text(out.strip()[:200] or "fetch failed", "red")))
            where.update(f"[red]codeshare unreachable[/]  [dim]{escape(url)}[/]")
            return None
        scripts, site_pages = parse_codeshare(out)
        self.found, self.found_for = scripts, self.needle or None
        if not self.needle:
            self.pages = site_pages
        return scripts

    def label(self) -> str:
        return f"search {self.needle}" if self.needle else "browse"

    @on(ListView.Selected, "#hits")
    def picked(self, event: ListView.Selected) -> None:
        if isinstance(item := event.item, ValueItem) and item.value:
            self.dismiss(item.value)

    def action_next(self) -> None:
        if self.page < self.pages:
            self.page += 1
            self.load()

    def action_prev(self) -> None:
        if self.page > 1:
            self.page -= 1
            self.load()

    def action_reload(self) -> None:
        self.found_for = None            # force the download again
        self.load()

    def action_close(self) -> None:
        self.dismiss(None)


class DevicePanel(Vertical):
    """One attached device: stats, a log, and a pty for whatever is running.

    Everything that is not the device family lives here — the log, the stats
    line, the streams, the pty, what the panel is pointed at — and a
    subclass says how that family is actually reached. frida is shared too:
    the server has to match the local client whatever the device is, it comes
    from the same releases, and only the path it goes to, the name of its
    architecture and how a shell is opened differ between an Android phone and
    a jailbroken iPhone.
    """

    can_focus = True
    kind = "device"                 # the family, as the interface names it
    installs = ""                   # what the installer picks off the host
    home_dir = "/"                  # where the file browser opens on the device
    staging_dir = ""                # where a copy the device refuses is landed first
    server_path = ""                # where frida-server lives on the device
    server_junk = ""                # what frida-server leaves beside itself
    frida_platform = ""             # what the frida releases call this family
    frida_ps = ""                   # a device command printing frida-server's pid
    # What a pid looks like in that command's output. Android's pgrep prints
    # bare pids; iOS asks for the whole process table and picks its line here,
    # because grep is not on every phone — see IOS_PS.
    frida_re = r"^\s*(\d+)\b"
    mirror_tool = ""                # what mirrors the screen into a window
    log_stream = "log"              # what this family calls its log

    def __init__(self, serial: str, app: MOABile) -> None:
        super().__init__(classes="panel")
        self.serial = serial
        self.mob = app
        # Nothing here outlives the run. A file remembering which app was
        # being poked at, and which account reaches the phone, is a record of
        # the work sitting on the machine afterwards — and this is a tool for
        # leaving nothing behind, on the device or off it.
        self.package: str | None = None
        self.frida_args: str = ""
        self.remote_dir: str = self.home_dir
        self.local_dir: str = str(Path.cwd())
        self.script_dir: str = str(Path.cwd())
        self.props: dict[str, str] = {}
        # Which readings the status poll has already reported on: see say_once().
        self._said: set[str] = set()
        self.packages: list[str] = []
        self.root = False
        self.mirror: subprocess.Popen | None = None
        self.streams: dict[str, asyncio.subprocess.Process] = {}
        # A line filter for the log stream, where narrowing it to one process
        # is this side's job rather than the tool's: see IosPanel.log_command.
        self.log_keep = ""
        # Streams asked for whose process is not up yet. The spawn is a worker,
        # so without this a second keypress starts a second logcat and the
        # first is left running with nothing holding it — the trap
        # TerminalPane.starting covers on the other side of the panel.
        self.starting: set[str] = set()

    def compose(self) -> ComposeResult:
        # The serial and what the device is live in the panel's own border, so
        # every row inside it belongs to the work rather than to the label.
        self.border_title = escape(short_serial(self.serial))
        self.border_subtitle = "reading device…"
        yield Static(id=f"stats-{self.uid}")
        # The command log is the panel; a tool like frida or objection opens
        # underneath it, so the log of what was run stays visible while the
        # REPL is up.
        # markup=False on purpose: everything is written as a Text object, so a
        # subprocess line containing "[/]" cannot be parsed as markup and crash.
        yield RichLog(id=f"log-{self.uid}", markup=False, wrap=True, max_lines=2000)
        yield TerminalPane(self)

    @property
    def uid(self) -> str:
        """Widget-id-safe form of the serial."""
        return re.sub(r"\W", "_", self.serial)

    @property
    def term(self) -> TerminalPane:
        return self.query_one(TerminalPane)

    def start_tool(self, argv: list[str], label: str = "") -> None:
        """Start a tool in this panel's pane, if the panel is still there.

        Every caller gets here after a modal or a device round trip, and the
        cable can come out in between — which takes the panel and the pane
        inside it with it. NoMatches: there is nothing left to look up, and
        nowhere left to say so either.
        """
        with contextlib.suppress(NoMatches):
            self.term.start(argv, label)

    def write(self, markup: str) -> None:
        """Log one of our own messages, with markup."""
        try:
            self.emit(Text.from_markup(markup))
        except MarkupError:
            self.emit(Text(markup))

    def say_stats(self, arrived: bool, out: str, how: str) -> None:
        """Whether the poll's readings came back, said once when they did not.

        A row of ? with no reason is the hardest thing in here to tell apart: a
        device that has gone away reads exactly like one whose own tools
        refused. Shared rather than written per family — the android side went
        without it for a long time precisely because it was written twice.
        """
        if arrived:
            self.said_ok("stats")
        else:
            self.say_once("stats",
                          f"stats unavailable: {out.strip()[:200] or f'no output {how}'}")

    def say_once(self, key: str, message: str, quiet: bool = False) -> None:
        """Report something the status poll would otherwise repeat forever.

        The poll runs every few seconds, so a phone that cannot answer one of
        its questions would fill the log with the same line — and reporting
        nothing at all is how a ? with no explanation happened in the first
        place. Once per reading, until that reading works again.

        Once per *key*, not per message: ssh folds the far end's stderr in
        wherever it arrives, so the same failure came back with its lines in a
        different order each poll — and a red toast every three seconds is
        worse than the missing number it was about. quiet is for the readings
        that are not failures at all: a phone reached over usb has no address
        to report, and there is nothing there to fix.
        """
        if key in self._said:
            return
        self._said.add(key)
        if quiet:
            self.write(f"[yellow]{escape(message)}")
        else:
            self.fail(message)

    def said_ok(self, key: str) -> None:
        """That reading works again: let its next failure be reported."""
        self._said.discard(key)

    def say_again(self) -> None:
        """Let every reading report itself again.

        Saying something once is about a poll repeating itself, not about a
        failure being old news forever. Point the panel at another account or
        another address and what it said about the last one is not an answer
        about this one — and a change made to fix something is exactly when
        whether it worked has to be on screen.
        """
        self._said.clear()

    def fail(self, message: str) -> None:
        """Log a failure and put it on screen.

        A red line in the log of a panel that is scrolled out of view is a
        silent failure, and these are the ones worth interrupting for. Plain
        text, never markup: half of these messages are device output.
        """
        self.emit(Text(message, "red"))
        self.mob.notify(message, title=self.serial, severity="error")

    def emit(self, text: Text) -> None:
        # is_attached, not is_mounted: see TerminalPane._spawn.
        if not self.is_attached:
            return
        # NoMatches: the panel was removed while a stream was still writing.
        with contextlib.suppress(NoMatches):
            self.query_one(f"#log-{self.uid}", RichLog).write(text)

    def _flush(self, buffer: list[str]) -> None:
        if buffer:
            lines, buffer[:] = list(buffer), []
            self.emit(Text("\n".join(lines)))

    # ------------------------------------------------------------ per family

    async def run(self, script: str, timeout: float = 15, root: bool = True) -> tuple[int, str]:
        """Run a shell command on the device, as root unless told otherwise."""
        raise NotImplementedError

    async def copy_in(self, local: str, remote: str) -> tuple[int, str]:
        """Copy host -> device with this family's tool, as the login user.

        The plain copy under push(), which is where the fallback lives:
        adb push, or scp down the tunnel. (exit code, what to report).
        """
        raise NotImplementedError

    @property
    def can_stage(self) -> bool:
        """Whether a refused copy is worth trying again through root.

        Root on android, a login that is not already root on ios; on a device
        with neither there is nothing staging could do that the copy did not.
        """
        raise NotImplementedError

    async def push(self, local: str, remote: str) -> tuple[int, str]:
        """Copy host -> device, through root where the plain copy is refused.

        Neither adb push nor scp is root even where the shell is, and the app's
        own directory and where frida-server goes are exactly what this is
        pointed at — the file browser's a key opens one of them. Only on
        failure, and only where there is a root to stage through: staging every
        transfer would copy each one twice for the sake of the one that needs
        it. One method for both families, so the key does one thing whichever
        device it is pressed on.
        """
        rc, out = await self.copy_in(local, remote)
        if rc != 0 and self.can_stage:
            return await self.push_as_root(local, remote)
        return rc, out

    async def push_as_root(self, local: str, remote: str) -> tuple[int, str]:
        """Land the file where the login user can write, then move it as root."""
        staged = f"{self.staging_dir}/{Path(local).name}"
        rc, out = await self.copy_in(local, staged)
        if rc != 0:
            return rc, out
        rc, out = await self.run(f"mv {shlex.quote(staged)} {shlex.quote(remote)}")
        if rc != 0:
            # Never leave the staged copy behind: it is the whole file, sitting
            # in a directory nobody asked for it to be in.
            await self.run(f"rm -f {shlex.quote(staged)}")
            return rc, out.strip() or f"could not move {staged} to {remote}"
        return 0, f"{local} -> {remote} (staged in {self.staging_dir}, moved as root)"

    async def pull(self, remote: str, local: str) -> tuple[int, str]:
        """Copy device -> host. (exit code, what to report)."""
        raise NotImplementedError

    async def describe(self) -> None:
        """Read what the device is into props, and say it in the border."""
        raise NotImplementedError

    async def load_packages(self) -> None:
        """The app list the sidebar filters, and the names behind it."""
        raise NotImplementedError

    async def stats(self) -> dict[str, str]:
        """batt, load, mem, ip, frida and pid, as the stats line wants them."""
        raise NotImplementedError

    async def package_chosen(self) -> None:
        """Anything this family has to look up once when the app changes."""

    async def system_info(self) -> None:
        """Dump what the device is into the log."""
        raise NotImplementedError

    def dump_sections(self, s: dict[str, list[str]], width: int) -> None:
        """A row per section of a batched dump, with frida-server's pid folded in.

        Whether frida-server is up belongs in a summary of what the device is,
        and it is the pid that belongs there — not the process table it was
        read out of, which is three hundred lines on a phone.

        A row is what the device has, not what it was asked for: the shell's
        word for a command or a path that is not there — magisk on a phone
        without it — is a dash. See not_there(). Everything here is
        device-supplied, so it is escaped, not trusted.
        """
        pid = self.frida_in(s.pop("ps", []))
        s["frida"] = [f"pid {pid}" if pid else "not running"]
        for key, lines in s.items():
            body = " · ".join(ln.strip() for ln in lines if ln.strip() and not not_there(ln))
            self.write(f"  [b]{key:<{width}}[/] {escape(body) or '-'}")

    async def install(self, path: str) -> tuple[int, str]:
        """Install an app package off the host. (exit code, what to report)."""
        raise NotImplementedError

    async def existing_exports(self, dest: str) -> list[Path]:
        """Paths of any exported files that already exist in dest."""
        return []

    async def save_app(self, dest: str) -> None:
        """Save the selected app's package into a host directory."""
        raise NotImplementedError

    async def shell_argv(self) -> tuple[list[str], str]:
        """(argv, label) for an interactive shell on the device."""
        raise NotImplementedError

    async def set_login(self) -> None:
        """Ask for whatever credentials this family needs, if it needs any."""
        self.write(f"[dim]{self.kind} needs no login: it is reached over the device's"
                   " own debug interface")

    def mirror_argv(self, index: int) -> list[str]:
        """The mirroring window for this device, as the index-th one open."""
        raise NotImplementedError

    async def log_command(self, pid: str) -> list[str]:
        """The device log: the whole device, or narrowed to one pid.

        A pid and not a package: it is the only thing both families can
        actually narrow by, and an app that is not running has none — so the
        caller decides whether there is a filter to be had and this is only
        asked how to apply it. See MOABile.action_log.
        """
        raise NotImplementedError

    async def app_pid(self) -> str | None:
        """The selected app's pid, if it is running at all."""
        raise NotImplementedError

    async def launch_app(self) -> bool:
        """Start the selected app, for the tools that can only attach.

        False where this device cannot start it at all — no launcher activity,
        no open(1) on the phone — which is not the same as an app that is on
        its way up, and is the difference between saying so now and waiting
        ten seconds first.
        """
        raise NotImplementedError

    async def wake_app(self) -> None:
        """Make the running app attachable, for the tools that only attach.

        Nothing to do here: on a family that leaves a process running off
        screen, a pid in the process table is a pid frida can hold.
        """

    async def data_dir(self) -> str:
        """Where the selected app keeps what it writes, or "" if not found."""
        return ""

    def server_arch(self) -> str | None:
        """The frida release architecture for this device, or None if unknown."""
        raise NotImplementedError

    def kill_frida(self, pid: str) -> str:
        """A device command that stops frida-server.

        kill, not pkill: a jailbroken phone has Darwin's ps but not always
        procps, and pkill is the half that is usually missing — and the pid is
        already in hand either way.
        """
        return f"kill -9 {pid}"

    @property
    def cpu(self) -> str:
        """What the device says its processor is, for a frida build to match."""
        return "?"

    def summary(self) -> str:
        """A few words naming the device, for the sidebar row."""
        return ""

    async def frida_blocker(self) -> str | None:
        """Why frida-server cannot run on this device, or None when it can."""
        return None

    # -------------------------------------------------------------- lifecycle

    async def load(self) -> None:
        await self.describe()
        await self.load_packages()
        await self.refresh_stats()

    async def refresh_stats(self) -> None:
        # is_attached, not is_mounted: see TerminalPane._spawn.
        if not self.is_attached:         # unplugged while a poll was in flight
            return
        now = await self.stats()
        if not self.is_attached:         # closed or unplugged while this was in flight
            return
        # ● and ○, the marks the device list already uses, with the pid beside
        # the ones that have one: "on pid 9001" three times over did not fit a
        # panel with another panel beside it.
        frida = f"[$success]●[/] {now['frida']}" if now.get("frida") else "[dim]○[/]"
        mirror = (f"[$success]●[/] {self.mirror.pid}"
                  if self.mirror and self.mirror.poll() is None else "[dim]○[/]")
        logs = "[$success]●[/]" if self.log_stream in self.streams else "[dim]○[/]"
        batt = f"{level}%" if (level := now.get("batt", "?")) != "?" else "?"
        # Suppressed as one block: the panel can be torn down between the check
        # above and here, and its children go first — so every child lookup in
        # this section has to be inside it.
        with contextlib.suppress(NoMatches):
            self.query_one(f"#stats-{self.uid}", Static).update(
                f"[dim]app  [/] [b]{escape(self.package or '-')}[/]"
                f"  [dim]pid[/] [b]{now.get('pid') or '-'}[/]\n"
                # No stray % on a battery nobody could read: "?%" reads as
                # a number that came back wrong rather than as one that never
                # came back.
                f"[dim]batt [/] {batt}   "
                f"[dim]load[/] {now.get('load') or '?'}   [dim]mem[/] {now.get('mem') or '?'}\n"
                # Escaped: the address can be the host this panel was
                # pointed at, which is whatever was typed at u, and
                # Static.update() has no fallback for markup it cannot parse.
                f"[dim]ip   [/] {escape(now.get('ip') or '?')}\n"
                f"[dim]frida[/] {frida}   [dim]{self.mirror_tool}[/] {mirror}"
                f"   [dim]{self.log_stream}[/] {logs}"
            )

    async def shutdown(self) -> None:
        """Kill everything this panel started; nothing outlives the TUI."""
        with contextlib.suppress(NoMatches):     # already partly torn down
            self.term.stop()
        reap(self.mirror)
        for name in list(self.streams):
            self.stop_stream(name)          # the same whole-group kill as a toggle

    # ------------------------------------------------------------ frida-server

    def frida_in(self, lines: list[str]) -> str | None:
        """frida-server's pid out of what frida_ps printed, or None.

        The first field of a line and nothing else. Any digit anywhere used to
        do, and then a shell that could not find `ps` answered `sh: 1: ps: not
        found` — and frida was reported as running on pid 1.
        """
        return next((m.group(1) for line in lines
                     if (m := re.match(self.frida_re, line))), None)

    async def frida_pid(self) -> str | None:
        """The pid of frida-server on the device, or None if it is not running."""
        _, out = await self.run(self.frida_ps, root=False)
        return self.frida_in(out.splitlines())

    async def toggle_frida(self) -> None:
        """Start frida-server, or stop it if it is already up."""
        if not (pid := await self.frida_pid()):
            await self.ensure_frida()
            return
        self.write(f"kill    {self.server_path} (pid {pid})")
        rc, out = await self.run(self.kill_frida(pid))
        if rc != 0 and out.strip():
            self.write(f"[red]{escape(out.strip())}")
        await asyncio.sleep(0.5)
        still = await self.frida_pid()
        if still:
            self.fail(f"frida-server is still running, pid {still}")
        else:
            self.write("[dim]frida-server stopped")
        await self.refresh_stats()

    async def purge_frida(self) -> None:
        """Stop frida-server and delete it, so the device keeps nothing of ours.

        Stopping it leaves tens of megabytes at a path anyone looking for it
        would recognise. Putting it back costs one push from the cache, so
        leaving nothing behind is cheap enough to be worth a key of its own.
        """
        junk = " ".join(filter(None, (self.server_path, self.server_junk)))
        if not await self.mob.push_screen_wait(ConfirmScreen(
                f"take frida-server off {self.serial}",
                f"stop it and delete {junk}",
                "leave it on the device")):
            return
        if pid := await self.frida_pid():
            self.write(f"kill    {self.server_path} (pid {pid})")
            await self.run(self.kill_frida(pid))
            await asyncio.sleep(0.5)
        rc, out = await self.run(f"rm -rf {junk}")
        if rc != 0 and out.strip():
            self.fail(out.strip())
        else:
            self.write(f"[dim]removed {junk}")
        await self.refresh_stats()

    async def ensure_frida(self) -> bool:
        """Make sure frida-server is running, installing it if needed. Verbose."""
        if pid := await self.frida_pid():
            self.write(f"frida-server already running, pid {pid} ({self.server_path})")
            await self.warn_drift()
            return True
        if blocker := await self.frida_blocker():
            self.fail(blocker)
            return False
        # The server must match the local client version exactly or attach fails.
        # Searched, not matched whole: sh() folds stderr in, and one deprecation
        # warning from the frida wheel used to read as "frida is not installed".
        _, out = await sh("frida", "--version")
        if not (found := re.search(r"\d+(?:\.\d+)+", out)):
            self.fail(f"frida did not report a version: {out.strip()[:80] or 'no output'}")
            return False
        ver = found.group()
        arch = self.server_arch()
        if arch is None:
            # Guessing here installs a binary the device cannot execute, and the
            # failure shows up later as an unexplained "did not stay up".
            self.fail(f"no frida-server build for {self.kind} cpu {self.cpu!r}")
            return False
        self.write(f"client  [b]frida {ver}[/] · device [b]{escape(self.cpu)}[/]"
                   f" -> server [b]{self.frida_platform}-{arch}[/]")
        # Something is already there: it may be a build someone put on the
        # device on purpose, or the same version we would push anyway, so
        # replacing it silently is the one thing not to do.
        if (there := await self.server_bytes()) is not None:
            self.write(f"found   [b]{self.server_path}[/] already on the device"
                       f" ({there // 1024} KiB)")
            if not await self.mob.push_screen_wait(ConfirmScreen(
                f"{self.server_path} is already on {self.serial} ({there // 1024} KiB)",
                f"replace it with the build matching frida {ver} ({arch})",
                "start the one that is already there",
            )):
                return await self.launch_server("the frida-server already on the device")
        if (payload := await self.server_files(ver, arch)) is None:
            return False
        for local, remote in payload:
            self.write(f"push    [b]{local.name}[/] -> [b]{remote}[/]"
                       f"  [dim]({local.stat().st_size // 1024} KiB)[/]")
            rc, out = await self.push(str(local), remote)
            if rc != 0:
                self.fail(f"push failed: {out.strip()}")
                return False
        return await self.launch_server(f"frida-server {ver} ({arch})")

    async def warn_drift(self) -> None:
        """Say so when the server on the device is not the client's version.

        The two have to match exactly, and the error frida prints when they do
        not names neither number — so a mismatch reads as a broken device
        rather than as the one-line fix it is.
        """
        _, out = await sh("frida", "--version")
        here = re.search(r"\d+(?:\.\d+)+", out)
        _, out = await self.run(f"{self.server_path} --version")
        there = re.search(r"\d+(?:\.\d+)+", out)
        if here and there and here.group() != there.group():
            self.fail(f"frida-server {there.group()} on the device, frida {here.group()} here"
                      " — they have to match: p removes it, then f installs the right one")

    async def server_files(self, ver: str, arch: str) -> list[tuple[Path, str]] | None:
        """(local file, where it goes on the device) for everything frida needs."""
        raise NotImplementedError

    def prune_cache(self, ver: str) -> None:
        """Keep one version's worth. The server has to match the local client
        exactly, so a build for a frida that has since been upgraded past will
        never be pushed again — and each one is tens of megabytes.

        Nowhere to cache is not fatal: XDG_CACHE_HOME or HOME can be somewhere
        this cannot write, and the fetch that follows says so in one line. An
        OSError out of here is a worker exception, which takes the whole app
        and every panel's record of the work with it.
        """
        try:
            CACHE.mkdir(parents=True, exist_ok=True)
        except OSError:
            return
        for stale in CACHE.iterdir():
            if f"-{ver}-" in stale.name or f"_{ver}_" in stale.name:
                continue
            if stale.is_dir():
                shutil.rmtree(stale, ignore_errors=True)
            else:
                stale.unlink(missing_ok=True)

    async def download(self, url: str, into: Path, pipe: str = "") -> bool:
        """Fetch url into a file, optionally through a decompressor.

        Anything short is a cut connection or an error page, never a build:
        pushing one of those fails on the device with nothing that says why.
        """
        self.write(f"fetch   {url}")
        # Quoted: the cache directory comes from HOME or XDG_CACHE_HOME, and
        # one apostrophe there ended the string and handed the rest of the
        # path to the shell as commands.
        rc, out = await sh("sh", "-c",
                           f"curl -fsSL {shlex.quote(url)}{pipe} > {shlex.quote(str(into))}",
                           timeout=600)
        if rc != 0 or not into.exists() or into.stat().st_size < MIN_SERVER_BYTES:
            size = into.stat().st_size if into.exists() else 0
            into.unlink(missing_ok=True)
            self.fail(f"download failed ({size} bytes): {out.strip()[:200]}")
            return False
        self.write(f"fetched {into.stat().st_size // 1024} KiB")
        return True

    async def server_bytes(self) -> int | None:
        """Size of the frida-server already on the device, or None if there is none.

        wc, not `ls -l`: its output is one number on every toybox, busybox and
        Darwin build, where the columns of ls are not.
        """
        _, out = await self.run(f"[ -f {self.server_path} ] && wc -c < {self.server_path}")
        return next((int(tok) for tok in out.split() if tok.isdigit()), None)

    async def launch_server(self, what: str) -> bool:
        """chmod and start whatever is at server_path, then confirm it stayed up."""
        self.write(f"chmod   755 {self.server_path}")
        await self.run(f"chmod 755 {self.server_path}")
        self.write(f"exec    nohup {self.server_path} &   [dim](as root)[/]")
        # </dev/null as well as the redirected output: over ssh the channel
        # stays open while anything still holds stdin, and the call that
        # started the server would never return.
        await self.run(f"nohup {self.server_path} >/dev/null 2>&1 </dev/null &")
        await asyncio.sleep(1)
        pid = await self.frida_pid()
        if pid:
            self.write(f"[green]{what} is up, pid {pid}[/]")
        else:
            self.fail("frida-server did not stay up — check root and the architecture")
        await self.refresh_stats()
        return pid is not None

    # ----------------------------------------------------------------- output

    def stop_stream(self, name: str) -> bool:
        """Stop a running stream. True if there was one."""
        if proc := self.streams.pop(name, None):
            # The whole group: killing adb alone leaves whatever it spawned
            # holding the pipe open, so the reader never sees EOF and the
            # stream never reports that it ended.
            with contextlib.suppress(ProcessLookupError, OSError):
                os.killpg(os.getpgid(proc.pid), signal.SIGKILL)
            with contextlib.suppress(ProcessLookupError):
                proc.kill()
            return True
        return False

    def start_stream(self, name: str, *cmd: str, keep: str = "") -> None:
        """Run a long-running command whose output lands in this panel.

        `keep` drops every line that does not contain it, for a stream the tool
        itself cannot narrow: idevicesyslog filters by process name and by
        nothing else, and the pid is the precise question. See
        IosPanel.log_command.
        """
        if not self.is_attached:         # unplugged while the question was up
            return
        if name not in self.streams and name not in self.starting:
            self.starting.add(name)
            self._stream(name, cmd, keep)

    @work
    async def _stream(self, name: str, cmd: tuple[str, ...], keep: str = "") -> None:
        def wanted(line: str) -> bool:
            return not keep or keep in line

        # A filter that keeps nothing looks exactly like a device with nothing
        # to say, and on the ios syslog it is usually neither: the unified
        # log's debug and info entries never reach that relay at all. Counted
        # so it can be said once, after enough has gone by to mean something.
        seen = kept = 0
        self.said_ok(f"{name}-quiet")     # a stream restarted is news again
        try:
            proc = await asyncio.create_subprocess_exec(
                *cmd, stdin=asyncio.subprocess.DEVNULL,
                stdout=asyncio.subprocess.PIPE, stderr=asyncio.subprocess.STDOUT,
                start_new_session=True,          # its own group, so it can be killed whole
            )
        except OSError as exc:                   # missing, not executable, no fork
            self.fail(f"{cmd[0]}: {exc.strerror or exc}")
            return
        finally:
            self.starting.discard(name)
        self.streams[name] = proc
        # The command, not "<name> started": the caller used to print one and
        # this the other, which said the same thing twice.
        self.write(f"[dim]$ {shlex.join(cmd)}")
        await self.refresh_stats()      # the stats line says what is running

        assert proc.stdout
        # logcat outruns the display: coalesce lines and repaint ten times a
        # second instead of once per line, and never grow the buffer unbounded.
        buffer: list[str] = []
        timer = self.set_interval(0.1, lambda: self._flush(buffer))
        try:
            # Chunks, not `async for line in stdout`: asyncio's readline() raises
            # ValueError once a line passes its 64 KiB buffer, and one long
            # stack trace in logcat was enough to take the whole app down.
            tail = b""
            while chunk := await proc.stdout.read(65536):
                *lines, tail = (tail + chunk).split(b"\n")
                for raw in lines:
                    seen += 1
                    if wanted(line := raw.decode(errors="replace").rstrip()):
                        kept += 1
                        buffer.append(line)
                if keep and not kept and seen > 300:
                    self.say_once(f"{name}-quiet",
                                  f"{seen} lines and none from {keep}: what the app logs"
                                  " may not reach this stream at all — l twice for"
                                  " everything on the device", quiet=True)
                if len(tail) > MAX_LINE_BYTES:      # no newline in sight: cut it loose
                    if wanted(cut := tail.decode(errors="replace")):
                        buffer.append(cut)
                    tail = b""
                if len(buffer) > 500:
                    del buffer[:-500]
            if tail and wanted(last := tail.decode(errors="replace").rstrip()):
                buffer.append(last)
        finally:
            timer.stop()
            self._flush(buffer)
            # Ours only: stopping a stream and starting it again puts a new
            # process under the same name, and forgetting that one here left
            # it running with nothing holding it.
            if self.streams.get(name) is proc:
                del self.streams[name]
        self.write(f"[dim]{name} ended")


class AndroidPanel(DevicePanel):
    """An Android device over adb, with root through su where it has it."""

    kind = "android"
    installs = ".apk"
    home_dir = "/sdcard"
    # The one directory adb can write to with no root, which is where a push
    # aimed somewhere it cannot write is landed before su moves it.
    staging_dir = ANDROID_TMP
    server_path = ANDROID_SERVER
    # frida-server opens its control socket in a directory of its own next to
    # the binary, and removing the binary alone leaves that behind.
    server_junk = ANDROID_FRIDA_SOCKET
    frida_platform = "android"
    frida_ps = ANDROID_FRIDA_PS
    mirror_tool = "scrcpy"
    log_stream = "logcat"

    async def adb(self, *args: str, timeout: float = 15) -> tuple[int, str]:
        return await sh("adb", "-s", self.serial, *args, timeout=timeout)

    async def su(self, script: str, timeout: float = 15) -> tuple[int, str]:
        """Run a script as root, whole.

        Quoted as one word: adb joins the arguments it is given and the shell
        on the device parses the lot again, so an unquoted script left its
        pipes, redirects and `&&` to that outer shell — only the first command
        of it ran as root — and `rm -f 'my file'` reached su as three
        arguments, which is a delete of the wrong files.
        """
        return await self.adb("shell", "su", "-c", shlex.quote(script), timeout=timeout)

    async def run(self, script: str, timeout: float = 15, root: bool = True) -> tuple[int, str]:
        """Through su where there is root, so /data/data is reachable at all."""
        return await (self.su(script, timeout) if self.root and root
                      else self.adb("shell", script, timeout=timeout))

    async def copy_in(self, local: str, remote: str) -> tuple[int, str]:
        self.write(f"[dim]$ adb push {shlex.join([local, remote])}")
        rc, out = await self.adb("push", local, remote, timeout=600)
        return rc, out.strip() or ("adb push failed" if rc else f"{local} -> {remote}")

    @property
    def can_stage(self) -> bool:
        # adb push is not root even where the shell is, exactly as adb pull is
        # not — and /data/data, where the browser's a key goes, is behind su.
        return self.root

    async def pull(self, remote: str, local: str) -> tuple[int, str]:
        self.write(f"[dim]$ adb pull {shlex.join([remote, local])}")
        rc, out = await self.adb("pull", remote, local, timeout=600)
        # adb pull is not root even where the shell is, so a file it refuses is
        # read back through su instead. Directories are left to adb.
        if rc != 0 and self.root and not remote.endswith("/"):
            return await self.cat_out(remote, local)
        return rc, out.strip() or ("adb pull failed" if rc else f"{remote} -> {local}")

    async def cat_out(self, target: str, local: str) -> tuple[int, str]:
        """Read a root-only file out through su, since adb pull is not root.

        Down a pipe into the file rather than collected first: what needs root
        is a database or a keystore, and holding one of those whole in this
        process is a copy nobody asked for. Into a ".part" beside it and moved
        over the destination only once the read finished — this runs after adb
        pull has already refused, and a file that was on the host before must
        not end up replaced by half of one. With the same deadline everything
        else gets: a device that goes away mid-read leaves adb blocked forever.
        """
        dest = Path(local)
        dest = dest / target.rsplit("/", 1)[-1] if dest.is_dir() else dest
        part = dest.with_name(dest.name + ".part")
        err = b""
        try:
            with part.open("wb") as sink:
                proc = await asyncio.create_subprocess_exec(
                    "adb", "-s", self.serial, "exec-out", "su", "-c",
                    # Quoted twice on purpose: once for the shell on the device
                    # that adb's own argument joining hands this to, once for
                    # the shell su runs it in. See AndroidPanel.su.
                    shlex.quote(f"cat {shlex.quote(target)}"),
                    stdin=asyncio.subprocess.DEVNULL, stdout=sink,
                    stderr=asyncio.subprocess.PIPE, start_new_session=True,
                )
                try:
                    _, err = await asyncio.wait_for(proc.communicate(), 600)
                except (asyncio.TimeoutError, TimeoutError):
                    with contextlib.suppress(ProcessLookupError, OSError):
                        os.killpg(os.getpgid(proc.pid), signal.SIGKILL)
                    await proc.wait()
                    err = f"{target}: timed out after 600s".encode()
            size = part.stat().st_size
            if proc.returncode or not size:
                return 1, (err.decode(errors="replace").strip()
                           or f"{target}: unreadable even as root")
            part.replace(dest)
        except OSError as exc:                 # adb gone, nowhere to write, no room
            return 1, f"{part}: {exc.strerror or exc}"
        finally:
            # Every way out but the one that moved it into place, cancellation
            # included: half a file under a name nobody chose is litter.
            part.unlink(missing_ok=True)
        return 0, f"{dest} ({size} bytes, via su)"

    @property
    def cpu(self) -> str:
        return self.props.get("ro.product.cpu.abi", "?")

    def summary(self) -> str:
        return self.props.get("ro.product.model", "")

    def server_arch(self) -> str | None:
        return ABIS.get(self.cpu)

    async def server_files(self, ver: str, arch: str) -> list[tuple[Path, str]] | None:
        """One binary, published ready to run."""
        self.prune_cache(ver)
        local = CACHE / f"frida-server-{ver}-{self.frida_platform}-{arch}"
        if local.exists() and local.stat().st_size >= MIN_SERVER_BYTES:
            self.write(f"cached  [b]{local}[/] ({local.stat().st_size // 1024} KiB)")
        elif not await self.download(
                f"{FRIDA_RELEASES}/{ver}/frida-server-{ver}-{self.frida_platform}-{arch}.xz",
                local, pipe=" | xz -d"):
            return None
        return [(local, self.server_path)]

    async def frida_blocker(self) -> str | None:
        return None if self.root else "frida-server needs root; without it use objection patchapk"

    async def describe(self) -> None:
        rc, out = await self.adb("shell", "getprop")
        # Only what a run that worked printed, and the same reasoning as the
        # ios side: adb folds its own errors into the output, and a device that
        # stopped answering otherwise reads as one with no properties — a panel
        # of ? with nothing saying why.
        #
        # The value is greedy to the final bracket: getprop values legitimately
        # contain "]" and a value-side character class silently dropped them.
        self.props = {} if rc else dict(re.findall(r"^\[([^\]]+)\]: \[(.*)\]$",
                                                  out, re.MULTILINE))
        if not self.props:
            self.fail(f"{last_line(out) or 'getprop said nothing'} for {self.serial}"
                      " — the device stopped answering adb; replug it, then r")
        _, who = await self.adb("shell", "su", "-c", "id")
        self.root = "uid=0" in who
        # Escaped: these come from the device. Static.update() has no fallback
        # for bad markup, so a model name containing "[/]" would take the panel
        # down the way logcat lines once took down the log.
        model = escape(self.props.get("ro.product.model", "?"))
        release = escape(self.props.get("ro.build.version.release", "?"))
        sdk = escape(self.props.get("ro.build.version.sdk", "?"))
        # The codename is what the device calls itself in a shell prompt, so
        # the panel and the prompt name the same thing: "Mi 9T · davinci".
        code = escape(self.props.get("ro.product.device", ""))
        self.border_title = (f"{escape(short_serial(self.serial))}  {model}"
                             + (f" · {code}" if code else ""))
        self.border_subtitle = (f"android {release} · api {sdk} · "
                                + ("[$success]root[/]" if self.root else "[$error]no root[/]"))
        self.write("[green]root: yes — su works[/]" if self.root else
                   "[red]root: no — su is missing or refused, so frida-server"
                   " and /data/data are out of reach[/]")

    async def load_packages(self) -> None:
        """The apps installed on the device, which is also what an install changes.

        -3, so the system's own packages stay out of it: a few hundred rows of
        com.android.* are not what anything here is pointed at, and the ios
        side asks for the same half by leaving --all off.
        """
        _, pkgs = await self.adb("shell", "pm", "list", "packages", "-3")
        # is_package: what comes back is a path on this machine as soon as e
        # saves the apk under it.
        self.packages = sorted(name for ln in pkgs.splitlines()
                               if is_package(name := ln.strip().removeprefix("package:")))
        if not self.packages:
            self.write("[yellow]no apps listed — check that adb reaches the device:"
                       f" {escape(last_line(pkgs)) or 'it said nothing'}")

    async def stats(self) -> dict[str, str]:
        # One shell round trip per tick. Separate adb calls per field made the
        # interface visibly lag with two devices attached.
        batch = (
            "echo @batt; dumpsys battery | grep -i 'level:';"
            "echo @load; cat /proc/loadavg;"
            "echo @mem; grep -E 'MemTotal|MemAvailable' /proc/meminfo;"
            "echo @ip; ip route;"
            f"echo @frida; {self.frida_ps};"
        )
        if self.package:
            batch += f"echo @pid; pidof {shlex.quote(self.package)};"
        # Not the exit status: a batch exits with its last command's, and the
        # last two are allowed to fail — pgrep prints nothing and exits 1 with
        # frida-server stopped, pidof the same with the app not running — so
        # the status reported a poll that answered in full as unanswered. The
        # marker is echoed by the device only if the shell ran at all, which is
        # the question being asked here.
        _, out = await self.adb("shell", batch)
        s = sections(out)
        self.say_stats("batt" in s, out, "from adb")
        total = first(s, "mem", r"MemTotal:\s+(\d+)")
        avail = first(s, "mem", r"MemAvailable:\s+(\d+)")
        # GB with one decimal: two panels side by side leave a stats line about
        # forty columns wide, and megabytes wrapped it onto a second row.
        mem = (f"{(int(total) - int(avail)) / 1e6:.1f}/{int(total) / 1e6:.1f} GB"
               if total and avail else "?")
        return {
            "batt": first(s, "batt", r"level:\s*(\d+)") or "?",
            "load": first(s, "load", r"^([\d.]+)") or "?",
            "mem": mem,
            "ip": self.address(s),
            "frida": self.frida_in(s.get("frida", [])) or "",
            "pid": first(s, "pid", r"^\s*(\d+)\b") or "-",
        }

    def address(self, s: dict[str, list[str]]) -> str:
        """What the stats line's address row says, in three falling steps.

        The device's own answer out of `ip route`; failing that the host adb
        was pointed at, which is an address only for a device reached with
        `adb connect`; failing that `usb`, because a device on the end of a
        cable with nothing on the network has none to show — the same answer
        the ios side gives for the same reason, rather than a `?` that reads
        as a number which came back wrong. See IosPanel.address.

        `?` is kept for the reading that never happened: the marker is echoed
        by the device only if the shell ran at all.
        """
        if "ip" not in s:
            return "?"
        if mine := first(s, "ip", r"src (\d+\.\d+\.\d+\.\d+)"):
            return mine
        # `adb connect` puts the address in the serial itself; a cable does not.
        host, _, port = self.serial.rpartition(":")
        return host if host and port.isdigit() else "usb"

    async def system_info(self) -> None:
        """Dump what the device is, in one shell round trip."""
        batch = (
            "echo @model; getprop ro.product.manufacturer; getprop ro.product.model;"
            "getprop ro.product.device; getprop ro.product.cpu.abilist;"
            "echo @build; getprop ro.build.fingerprint;"
            "echo @patch; getprop ro.build.version.security_patch;"
            "echo @kernel; uname -r;"
            "echo @uptime; uptime;"
            "echo @selinux; getenforce;"
            "echo @crypto; getprop ro.crypto.state; getprop ro.crypto.type;"
            "echo @debug; getprop ro.debuggable; getprop ro.secure;"
            "echo @adbtcp; getprop service.adb.tcp.port;"
            "echo @proxy; settings get global http_proxy;"
            "echo @timezone; getprop persist.sys.timezone;"
            "echo @screen; wm size; wm density;"
            "echo @storage; df -h /data;"
            "echo @net; ip -o -4 addr show scope global;"
            "echo @su; command -v su; ls -d /sbin/.magisk /data/adb/magisk;"
            f"echo @ps; {self.frida_ps};"
        )
        _, out = await self.adb("shell", batch, timeout=30)
        self.write(f"[b]system  {escape(self.serial)}[/]")
        # Eight columns: timezone is the longest key this dump has.
        self.dump_sections(sections(out), 8)
        self.write(f"  [b]{'root':<8}[/] "
                   + ("[green]yes — su works[/]" if self.root else
                      "[red]no — su is missing or refused[/]"))

    async def install(self, path: str) -> tuple[int, str]:
        self.write(f"[dim]$ adb install -r {path}")
        rc, out = await self.adb("install", "-r", path, timeout=600)
        # "Failure [...]" with an exit status of 0 is how most builds report a
        # refused install, so the status alone is not the answer.
        if rc == 0 and "Failure" in out:
            rc = 1
        # The one an apk repackaged by objection always hits: -r updates an
        # app, but it cannot re-sign it, and android refuses a new signature
        # over an old one. Uninstalling is the fix and it takes the app's data
        # with it, so it is said rather than done.
        if "UPDATE_INCOMPATIBLE" in out or "signatures do not match" in out:
            out += (f"\n  adb -s {self.serial} uninstall {self.package or '<package>'}"
                    "  first — that removes the app's data too")
        return rc, out.strip() or ("adb install failed" if rc else "installed")

    async def existing_exports(self, dest: str) -> list[Path]:
        """Paths of any apk files that already exist in dest."""
        _, out = await self.adb("shell", "pm", "path", self.package or "")
        paths = [ln.strip().removeprefix("package:") for ln in out.splitlines()
                 if ln.strip().startswith("package:")]
        targets = [Path(dest) / f"{self.package}-{p.rsplit('/', 1)[-1]}" for p in paths]
        return [local for local in targets if local.exists()]

    async def save_app(self, dest: str) -> None:
        """Pull the package's apk — base and every split — to the host.

        Named after the package rather than kept as base.apk: two packages
        pulled into the same directory both answer to that name.
        """
        rc, out = await self.adb("shell", "pm", "path", self.package or "")
        paths = [ln.strip().removeprefix("package:") for ln in out.splitlines()
                 if ln.strip().startswith("package:")]
        if rc != 0 or not paths:
            self.fail(out.strip()
                      or f"{self.package}: no apk listed for it — pm path said nothing")
            return
        for path in paths:
            local = Path(dest) / f"{self.package}-{path.rsplit('/', 1)[-1]}"
            rc, out = await self.pull(path, str(local))
            if rc == 0:
                self.write(escape(out))
            else:
                self.fail(out)

    async def shell_argv(self) -> tuple[list[str], str]:
        """A shell on the device, with a prompt that says where it is.

        `davinci:/data/local/tmp #` — the device's own codename, the working
        directory, and the mark that says whether this is root. `-t` forces a
        pty on the device: without one the shell is not interactive and prints
        no prompt at all, which is what made `su` look like a dead terminal.
        `ENV=` keeps mksh from sourcing /system/etc/mkshrc, which would set a
        prompt of its own over this one — and on some ROMs sets none.

        No `-i` and no `su -c`, both deliberate. A shell with a pty on stdin is
        interactive without being told, while `-i` forces it even when there is
        no terminal to be interactive on. And `su -c` runs its command in a new
        session, which leaves it without a controlling terminal: that is where
        "No controlling tty" and "won't have full job control" came from. Plain
        `su -p` keeps the session and the environment, so the prompt survives
        the switch to root; a su without `-p` falls back to its own prompt.
        """
        here = self.props.get("ro.product.device") or self.serial
        # Quoted rather than dropped between quotes: the codename is whatever
        # the ROM put in the prop, and an apostrophe in it closed the string.
        prompt = shlex.quote(f"{here}:$PWD {'#' if self.root else '$'} ")
        script = f"ENV= PS1={prompt} "
        script += "su -p || su" if self.root else "exec sh"
        # The PS1 plumbing is ours, not something the user asked for: the log
        # and the pane title say what this is, not how it is set up.
        return (["adb", "-s", self.serial, "shell", "-t", script],
                f"adb -s {self.serial} shell" + (" su" if self.root else ""))

    def mirror_argv(self, index: int) -> list[str]:
        """Tiled, so a second device's window does not land on the first."""
        return ["scrcpy", "-s", self.serial, "--window-title", self.serial,
                "--window-x", str(60 + index * 420), "--window-y", "60",
                "--window-width", "400", "--window-height", "800"]

    async def log_command(self, pid: str) -> list[str]:
        args = ["adb", "-s", self.serial, "logcat", "-v", "brief"]
        if pid:
            # logcat's own --pid, which is exact and costs nothing here: the
            # device drops every other process before the line is ever sent.
            args.append(f"--pid={pid}")
        return args

    async def app_pid(self) -> str | None:
        _, out = await self.adb("shell", "pidof", self.package or "")
        return next((tok for tok in out.split() if tok.isdigit()), None)

    async def launch_app(self) -> bool:
        # monkey answers "No activities found to run" for an app whose
        # launcher activity is absent or disabled, and exits 0 either way — so
        # what it said is the only thing to read, and the sentence is the
        # difference between "would not start" and knowing why it would not.
        _, out = await self.adb("shell", "monkey", "-p", self.package or "",
                                "-c", "android.intent.category.LAUNCHER", "1")
        if "No activities found" in out or "monkey aborted" in out:
            self.write(f"[yellow]{escape(last_line(out)[:120])}")
            return False
        return True

    async def data_dir(self) -> str:
        # MASTG-TECH-0008: the internal one, which is where the databases and
        # the shared_prefs are. It is named after the package, so unlike the
        # ios side there is nothing to look up.
        return f"/data/data/{self.package}" if self.package else ""


class IosPanel(DevicePanel):
    """A jailbroken iPhone: usbmux for the device, ssh for its insides.

    libimobiledevice reaches the device without any cooperation from it, which
    is how the info dump, the syslog and installing an ipa work. A shell, the
    filesystem and frida-server all need ssh, so an iproxy tunnel is opened
    per panel — local port 2222 upwards to port 22 on the phone — and
    everything else goes down it.

    No key is ever installed on the phone: that would be a file of ours left
    on a device we are meant to leave clean. Instead one connection is
    authenticated with a password and held open as an ssh multiplexing
    master, and every command after it rides that socket without
    authenticating again — which is also what keeps a status poll every three
    seconds down to one round trip rather than a fresh handshake.
    """

    kind = "ios"
    installs = ".ipa"
    home_dir = "/var/mobile"
    # mobile's own directory: where a push sudo has to finish is landed first.
    staging_dir = home_dir
    # What frida's own releases call it, which is not what anybody else does:
    # the package is frida_<ver>_iphoneos-<arch>.deb.
    frida_platform = "iphoneos"
    frida_ps = IOS_PS
    frida_re = r"^\s*(\d+)\s+\S*frida-server"
    mirror_tool = "ioscpy"
    log_stream = "syslog"

    def __init__(self, serial: str, app: MOABile) -> None:
        super().__init__(serial, app)
        self.ssh_user: str = IOS_DEFAULT_USER
        # 127.0.0.1 means "down the tunnel"; anything else is the phone's own
        # address over the network, and then no tunnel is started at all.
        self.ssh_host: str = "127.0.0.1"
        self.ssh_port: int = 0
        self.tunnel: subprocess.Popen | None = None
        # The port the tunnel's command line was last logged for, so a tunnel
        # that flaps does not log one per poll: see tunnel_up(). Whether its
        # failure has already been reported is say_once's, under "tunnel-down".
        self._tunnel_shown = 0
        # The battery reading and how many polls it has left before it is
        # asked for again: see stats().
        self._batt, self._batt_due = "?", 0

        # The address found in this machine's arp table, and how many polls
        # it has left before it is looked up again: see wifi_address().
        self._arp, self._arp_due = "", 0
        # Whether the phone has said it has no command that names an address.
        # Kept once said: see address().
        self._no_ip_tool = False
        # Each app's executable and bundle path, as the app list gave them:
        # see load_packages(), package_chosen() and bundle_dir().
        self.executables: dict[str, str] = {}
        self.bundles: dict[str, str] = {}
        # The executable the selected app runs as, and the app it was looked
        # up for — None until the first lookup: see package_chosen().
        self.proc_name = ""
        self._proc_for: str | None = None
        # The ssh multiplexing master and the password that opened it. Kept in
        # memory for as long as the panel is open and written nowhere: a
        # password belongs on disk even less than a key belongs on the phone.
        self.master: subprocess.Popen | None = None
        # Its pty stays open for as long as it runs: closing the last handle on
        # a pty hangs up everything attached to it, which took the master down
        # the moment it had finished authenticating.
        self.master_fd: int | None = None
        self.password = IOS_DEFAULT_PASSWORD
        # One opener at a time: a status poll, a stats read and an action all
        # ask for the connection at once, and without this each would tear down
        # the master the others had just authenticated.
        self.master_lock = asyncio.Lock()
        # Whether a refused password has already been reported: like the
        # tunnel, this is asked for every three seconds and must be said once.
        self.master_said = False
        # /var/jb on a rootless jailbreak, where nothing lives where it used to.
        self.jb = ""

    @property
    def server_path(self) -> str:            # type: ignore[override]
        return f"{self.jb}/usr/sbin/frida-server"

    @property
    def server_junk(self) -> str:            # type: ignore[override]
        # The agent directory: pushed with the server, and useless without it.
        return f"{self.jb}/usr/lib/frida-1.0"

    @property
    def cpu(self) -> str:
        return self.props.get("CPUArchitecture", "?")

    def summary(self) -> str:
        return self.props.get("DeviceName", "") or self.props.get("ProductType", "")

    def server_arch(self) -> str | None:
        return IOS_ARCHS.get(self.cpu)

    # ------------------------------------------------------------------- ssh

    def control_path(self) -> str:
        # The uid is in the name: /tmp is shared, and a socket belonging to
        # someone else is a permission error ssh reports as a failed connection.
        # The host is in it too: down the tunnel the port alone is unique, but
        # two phones reached over the network are both port 22, and they would
        # otherwise share one socket — and open_master clears the socket it is
        # about to use.
        return str(Path(tempfile.gettempdir())
                   / f"moabile-{os.getuid()}-{self.ssh_host}-{self.ssh_port}")

    def ssh_argv(self, *args: str, batch: bool = True) -> list[str]:
        """ssh to this device, over the master where there is one.

        batch=False marks the connections that may have to authenticate — the
        master, and the shell when the master could not be opened. Those are
        the ones told to skip keys entirely; everything else rides the master's
        socket, has nothing to answer, and must fail rather than sit on a
        prompt nobody is watching.
        """
        opts = ["-p", str(self.ssh_port), *(SSH_OPTS if batch else SSH_LOUD_OPTS),
                "-o", "ControlMaster=auto",
                "-o", f"ControlPath={self.control_path()}"]
        # ControlPersist is what backgrounds a master, and the master here is a
        # process of ours we watch: told to persist, ssh forks the moment it has
        # authenticated and the process we are holding exits with nothing to say
        # — which open_master could only read as a refused password, so the
        # panel asked for one every single time it opened. Explicitly `no`
        # rather than merely left out: a ControlPersist in the user's own
        # ssh_config backgrounds it just the same.
        opts += (["-o", "BatchMode=yes", "-o", "ControlPersist=30"] if batch
                 else [*SSH_PASSWORD_OPTS, "-o", "ControlPersist=no"])
        return ["ssh", *opts, f"{self.ssh_user}@{self.ssh_host}", *args]

    async def master_alive(self) -> bool:
        """Whether the multiplexed connection is still there to be used."""
        rc, _ = await sh(*self.ssh_argv("-O", "check"), timeout=5)
        return rc == 0

    async def master_up(self) -> bool:
        """Make sure one authenticated connection is open for the rest to use.

        The default password every jailbreak ships with is tried first and
        never stored; when the phone's was changed, whoever is at the keyboard
        is asked once and the answer lives in memory until the panel closes.
        """
        if not await self.tunnel_up():
            return False
        # poll(), not `ssh -O check`: the socket exists exactly as long as the
        # process holding it does, and a fork per device command is not worth
        # asking a second time.
        if self.master and self.master.poll() is None:
            return True
        if self.master_said:      # asked already and refused: do not ask every poll
            return False
        async with self.master_lock:
            # Someone else may have opened it while this call waited its turn.
            if self.master and self.master.poll() is None:
                return True
            if not (said := await self.open_master(self.password)):
                self.master_said = False
                return True
            # Wrong password, or none yet: ask, once, with the field masked.
            if said.strip():
                # All of it, not the one line the summary keeps: when ssh is
                # unhappy the useful part is rarely the last thing it printed.
                self.write(f"[dim]{escape(said.strip()[:400])}[/]")
            typed = await self.mob.push_screen_wait(AskScreen(
                f"password for {self.ssh_user}@{self.ssh_host}", "",
                f"{said[:90]} — kept in memory only, never written to disk", secret=True))
            if not (typed := (typed or "").strip()):
                self.master_said = True
                self.write("[yellow]no password given — [b]u[/] sets the login and asks again")
                return False
            if said := await self.open_master(typed):
                self.master_said = True
                self.fail(f"ssh: {said[:120]}")
                return False
            self.password, self.master_said = typed, False
            return True

    async def open_master(self, password: str) -> str:
        """Open the master on a pty of its own, typing password at its prompt.

        ssh takes a password from a terminal and from nothing else, and there
        is deliberately no key to fall back on — so the one connection that
        has to authenticate gets a pty, off screen, and the password goes
        straight down it rather than onto a command line where `ps` would show
        it. Returns "" when the master is up, or what ssh said when it is not.
        """
        self.drop_master()
        # ssh unlinks its control socket when it is asked to close and not when
        # it is killed, so a crash, a SIGKILL or an older build leaves the file
        # behind — and `-M` will not reuse one it finds: "ControlSocket ...
        # already exists, disabling multiplexing", after which the master is
        # not a master, nothing can ride it, and the panel asks for a password
        # again on every open. Ask a live one to go; unlink what is left.
        if Path(self.control_path()).exists():
            await sh(*self.ssh_argv("-O", "exit"), timeout=5)
            Path(self.control_path()).unlink(missing_ok=True)
        argv = self.ssh_argv("-M", "-N", batch=False)
        try:
            # A controlling terminal, which is where ssh insists on reading a
            # password from — see spawn_on_pty(). SSH_ASKPASS_REQUIRE because
            # a DISPLAY set on this machine would otherwise send the prompt to
            # a graphical window nobody is looking at.
            proc, primary = spawn_on_pty(
                argv, env={**os.environ, "SSH_ASKPASS_REQUIRE": "never"})
        except OSError as exc:
            return f"ssh: {exc.strerror or exc}"
        os.set_blocking(primary, False)
        said, asked, was_off, seen = "", 0, False, -1

        def drain() -> None:
            """Read whatever ssh has said, with the password taken back out.

            Everything reported out of here — the refusal, the exit, the
            timeout — is a line of `said`, and `said` goes into the panel's
            log. The one path that answers on the prompt rather than on the
            echo going off is the path where echo may still be on, and there
            the password comes straight back as input the far end echoed. It
            is the one thing in this program that must not reach a log or an
            svg of the screen.
            """
            nonlocal said
            with contextlib.suppress(OSError):
                said += os.read(primary, 65536).decode(errors="replace")
            if password:
                said = said.replace(password, "***")

        try:
            for tick in range(SSH_MASTER_TICKS):
                await asyncio.sleep(0.1)
                drain()
                if seen < 0 and re.search(SSH_PROMPT, said, re.IGNORECASE):
                    seen = tick
                # Echo going off is ssh saying it is ready to be told a secret,
                # and waiting for that instead of answering the question the
                # instant it appears is the whole difference between this
                # working and not: ssh prints the prompt first and puts the
                # terminal into its reading mode a moment later, and that
                # switch throws away anything typed in between — so the
                # password went nowhere and the connection died unexplained.
                # The second clause is the way out on a platform where the
                # setting cannot be read back: answer a second after the
                # prompt, which no terminal is slower than.
                off = echo_off(primary)
                if (off and not was_off) or (0 <= seen <= tick - 10 and not asked):
                    asked += 1
                    if asked > 1:          # asked again: the one we gave is wrong
                        return last_line(said) or "the password was refused"
                    os.write(primary, password.encode() + b"\r")
                    said, seen = "", -1
                was_off = off
                if proc.poll() is not None:
                    # Drain first: ssh says why on its way out, and reporting
                    # the exit before reading that turned every failure into
                    # the same blank line.
                    drain()
                    last = last_line(said) or "ssh exited without saying why"
                    if not asked and "denied" in last.lower():
                        # It never asked. The phone offers no method we can
                        # answer, which is a setting on the phone, not here.
                        last += " — sshd on the phone allows no password:"
                        last += " check PasswordAuthentication and"
                        last += " KbdInteractiveAuthentication in sshd_config"
                    return last
                if asked and tick % 5 == 0 and await self.master_alive():
                    # Only now: a refused ssh sits there re-prompting, alive but
                    # carrying nothing, and taking that for the master is how a
                    # wrong password came back as a working connection.
                    self.master, self.master_fd = proc, primary
                    return ""
            return last_line(said)[:120] or "ssh did not answer"
        finally:
            if self.master is not proc:
                os.close(primary)
                reap(proc)

    def drop_master(self) -> None:
        """Close the multiplexed connection, so the next one authenticates again."""
        reap(self.master)
        if self.master_fd is not None:
            with contextlib.suppress(OSError):
                os.close(self.master_fd)
            self.master_fd = None
        self.master = None

    async def tunnel_up(self) -> bool:
        """Make sure iproxy is forwarding a local port to port 22 on the phone."""
        if self.ssh_host != "127.0.0.1":       # reached over the network instead
            return True
        if self.tunnel and self.tunnel.poll() is None:
            return True
        if not self.pick_port():
            return False
        argv = await iproxy_argv(self.ssh_port, self.serial)
        try:
            # Popen, not create_subprocess_exec: the tunnel outlives this call
            # and is only ever polled and terminated, so an awaitable handle
            # for it would be a coroutine nobody is in a position to await.
            self.tunnel = tunnel = subprocess.Popen(  # noqa: ASYNC220
                argv, stdin=subprocess.DEVNULL,
                stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL,
                start_new_session=True,
            )
        except OSError as exc:
            return self.no_tunnel(f"iproxy: {exc.strerror or exc}")
        # Half a second for a refused iproxy to fall over — it binds its port
        # before it has anything to say about the phone, so the bind alone is
        # not proof it will stay up.
        await asyncio.sleep(0.5)
        # Then wait for it to be listening, which is the only signal it gives
        # that it is up; it has to be, before the first ssh. Waiting for the
        # signal rather than for the clock alone is what makes this right on a
        # loaded machine, where half a second was not always enough for a
        # refused iproxy to have exited yet and the tunnel was called up.
        # port_listening, not port_free: see it for why this one connects.
        for _ in range(TUNNEL_TICKS):
            if tunnel.poll() is not None or port_listening(self.ssh_port):
                break
            await asyncio.sleep(0.1)
        # The local, and then whether it is still the panel's: a login changed
        # with u or a panel closed while this waited, and drop_tunnel terminated
        # this very process and put None in its place. Reaching into
        # self.tunnel here took the worker down with an AttributeError, and
        # reporting the terminate below blamed the phone for it.
        if self.tunnel is not tunnel:
            return False
        if tunnel.poll() is not None:
            # The port was free a moment ago, so this is the phone, not the
            # port: usbmux refuses a device it has no pairing record for.
            return self.no_tunnel(f"iproxy exited at once on port {self.ssh_port}"
                                  " — unlock the phone and accept the trust dialog, then r")
        # The command line once per port, not once per tunnel: a tunnel that
        # comes up and then dies is started again by the very next poll, and
        # logging each of those put a line in the panel every three seconds for
        # as long as it flapped. That it is flapping is worth exactly one line.
        if self._tunnel_shown != self.ssh_port:
            self.write(f"[dim]$ {shlex.join(argv)}")
            self._tunnel_shown = self.ssh_port
        else:
            self.say_once("tunnel", f"the usb tunnel on port {self.ssh_port} keeps"
                          " dropping and is being started again each poll — unlock"
                          " the phone, or replug it and press r", quiet=True)
        self.said_ok("tunnel-down")     # a later failure is news again
        return True

    def pick_port(self) -> bool:
        """Make sure this panel's local port is one it can actually have.

        Checked against the other open panels and against the machine itself:
        the port is remembered per device, and a tunnel some earlier run left
        behind holds one this panel would otherwise retry every three seconds
        forever.
        """
        used = {p.ssh_port for p in self.mob.panels if isinstance(p, IosPanel) and p is not self}
        if self.ssh_port and self.ssh_port not in used and port_free(self.ssh_port):
            return True
        free = (port for port in range(IOS_SSH_PORT, IOS_SSH_PORT + 64)
                if port not in used and port_free(port))
        if (found := next(free, 0)) == 0:
            return self.no_tunnel(f"no free local port between {IOS_SSH_PORT} and"
                                  f" {IOS_SSH_PORT + 63} for the tunnel")
        self.ssh_port = found
        return True

    def no_tunnel(self, message: str) -> bool:
        """Say the tunnel will not come up, once rather than once per poll.

        The status poll asks for a tunnel every three seconds, so a phone
        whose iproxy will not start used to put an error toast and two log
        lines on screen every three seconds for as long as it stayed plugged
        in — burying whatever else the panel had to say. The same say-once the
        rest of the readings use, so u clears this one along with them.
        """
        self.say_once("tunnel-down", message)
        return False

    def no_connection(self) -> tuple[int, str]:
        """What a command reports when the master could not be opened."""
        return 1, f"no ssh connection to {self.ssh_user}@{self.ssh_host}:{self.ssh_port}"

    async def run(self, script: str, timeout: float = 15, root: bool = True) -> tuple[int, str]:
        """Run a command on the phone — as root only when it has to be.

        Reading the load, the memory, the address and the process list needs
        nothing mobile does not already have, and those are the commands this
        asks for every three seconds. Sending them through sudo bought no
        access and cost a password round trip each time — and where sudo was
        not set up at all, it was the whole reason the stats line said `?`.
        """
        if not await self.master_up():
            return self.no_connection()
        script, feed = self.as_root(script) if root else (IOS_PATH + script, b"")
        return await sh(*self.ssh_argv(script), timeout=timeout, feed=feed)

    def as_root(self, script: str) -> tuple[str, bytes]:
        """The script, and the stdin that gets it run as root.

        Through sudo where the login is not root, the way the android side goes
        through su: frida-server, /var/containers and the app bundles are all
        out of mobile's reach. `-S -p ''` makes sudo take the password from
        stdin and print no prompt of its own, so it works whether or not the
        account is NOPASSWD — and the password stays off every command line,
        where anyone on this machine could read it out of `ps`.
        """
        if self.ssh_user == "root":
            return IOS_PATH + script, b""
        # Both sides of sudo: the outer shell has to find sudo itself, which on
        # a rootless jailbreak is under /var/jb, and the shell sudo starts gets
        # secure_path instead of whatever it was handed. See IOS_PATH.
        return (f"{IOS_PATH}sudo -S -p '' sh -c {shlex.quote(IOS_PATH + script)}",
                self.password.encode() + b"\n")

    async def scp(self, source: str, dest: str) -> tuple[int, str]:
        """scp with the tunnel's port and the same options ssh gets.

        -r throughout: an app bundle is a directory, and scp of a single file
        does not mind being told it may recurse.
        """
        if not await self.master_up():
            return self.no_connection()
        argv = ["scp", "-r", "-P", str(self.ssh_port), *SSH_OPTS,
                "-o", "BatchMode=yes", "-o", f"ControlPath={self.control_path()}",
                source, dest]
        self.write(f"[dim]$ {shlex.join(argv)}")
        return await sh(*argv, timeout=600)

    async def copy_in(self, local: str, remote: str) -> tuple[int, str]:
        rc, out = await self.scp(local, f"{self.ssh_user}@{self.ssh_host}:{remote}")
        return rc, out.strip() or ("scp failed" if rc else f"{local} -> {remote}")

    @property
    def can_stage(self) -> bool:
        # scp runs as the login user, so as mobile it cannot write where
        # frida-server has to go; sudo is what moves it there.
        return self.ssh_user != "root"

    async def pull(self, remote: str, local: str) -> tuple[int, str]:
        """Stream it out as a tar rather than copying it file by file.

        What comes off a phone is usually an app bundle: hundreds of files with
        symlinks among them, over a usb tunnel. `scp -r` asks for each one in
        turn and, since OpenSSH 9 put it on top of sftp, resolves the symlinks
        instead of copying them — so a repacked bundle is not the one that was
        on the device. One tar is one round trip and keeps the tree as it is.

        MASTG-TECH-0053 writes that tar to /tmp on the phone and scps it back.
        This pipes it instead: same archive, nothing left behind on the device.
        `local` is the directory it unpacks into, which is what both callers
        have and what scp was being handed anyway.
        """
        if not await self.master_up():
            return self.no_connection()
        parent, _, name = remote.rstrip("/").rpartition("/")
        script, feed = self.as_root(
            f"tar cf - -C {shlex.quote(parent or '/')} {shlex.quote(name)}")
        # An ssh that fails sends no archive, and tar exits non-zero on the
        # empty stream — so the pipeline still reports the failure, with what
        # ssh said about it folded into the output.
        pipe = f"{shlex.join(self.ssh_argv(script))} | tar xf - -C {shlex.quote(local)}"
        self.write(f"[dim]$ ssh … tar cf - {escape(name)} | tar xf - -C {escape(local)}")
        rc, out = await sh("sh", "-c", pipe, timeout=600, feed=feed)
        return rc, out.strip() or ("pull failed" if rc else f"{remote} -> {local}")

    async def shutdown(self) -> None:
        await super().shutdown()
        await self.drop_tunnel()

    async def drop_tunnel(self) -> None:
        """Close the multiplexed ssh master and the tunnel underneath it.

        The master holds an authenticated session and the tunnel under it
        outlives everything unless it is asked to go — so both go together,
        whether the panel is closing or the login it was opened for has just
        changed.
        """
        if self.ssh_port:
            await sh(*self.ssh_argv("-O", "exit"), timeout=5)
        self.drop_master()
        self._tunnel_shown = 0          # the next one is a new tunnel, and news
        reap(self.tunnel)
        self.tunnel = None

    # ------------------------------------------------------------- the device

    async def describe(self) -> None:
        rc, out = await sh("ideviceinfo", "-u", self.serial, timeout=20)
        # Only what a run that worked printed. sh() folds stderr in, and
        # "ERROR: Could not connect: pairing" is `key: value` shaped — so an
        # untrusted phone parsed as a device with one property called ERROR,
        # and the line below, which is the whole point of it, never ran.
        #
        # Escaped where it is shown: a device name is whatever its owner typed,
        # and Static.update() has no fallback for markup it cannot parse.
        self.props = {} if rc else dict(re.findall(r"^([\w.]+): (.*)$", out, re.MULTILINE))
        if not self.props:
            self.fail(f"{last_line(out) or 'ideviceinfo said nothing'} for {self.serial}"
                      " — accept the trust dialog on the phone, then r")
        name = escape(self.props.get("DeviceName", "?"))
        model = escape(self.props.get("ProductType", "?"))
        version = escape(self.props.get("ProductVersion", "?"))
        self.border_title = f"{escape(short_serial(self.serial))}  {name}"
        # One ssh call for all three: whether it answers at all, whether that
        # is root, and whether this is a rootless jailbreak — which decides
        # where frida-server has to go.
        _, who = await self.run("id; [ -d /var/jb ] && echo @rootless")
        self.root = "uid=0" in who
        self.jb = "/var/jb" if "@rootless" in who else ""
        self.border_subtitle = (f"{model} · ios {version} · "
                                + ("[$success]ssh root[/]" if self.root else "[$error]no ssh[/]"))
        if self.root:
            self.write(f"[green]ssh: root on {self.ssh_user}@{self.ssh_host}:{self.ssh_port}"
                       + (f" · rootless jailbreak, {self.jb}[/]" if self.jb else "[/]"))
        else:
            self.write(f"[red]ssh: no root as {escape(self.ssh_user)}"
                       f" — {escape(who.strip()[:120])}[/]")
            self.write("[dim]needs OpenSSH running on the phone, and sudo for a login"
                       " that is not root. [b]u[/] sets which account to use.")

    async def load_packages(self) -> None:
        """Installed apps by bundle id, with the names the syslog filters on.

        The installer's list needs nothing running on the phone and carries
        each app's executable and its bundle path — the two lookups that would
        otherwise cost a glob grep over every Info.plist on the device. The
        current command line takes those as `--attribute`; the one before it
        printed three fixed columns and had no way to ask, which is the split
        installer_takes_commands() reads.

        The user's own apps and nothing else, which is what `list` answers with
        when `--all` is left off — the same half the android side asks for with
        -3. frida-ps would name the system's own on top of it, and a sidebar
        holding every com.apple.* is not what any of this is pointed at.
        """
        # Annotated: the two command lines answer with a different number of
        # columns, and the branch below is the whole reason this is read at all.
        columns: tuple[str, ...]
        if await installer_takes_commands():
            columns = IOS_APP_ATTRS
            args = ["list"]
            for attr in columns:
                args += ["-a", attr]
        else:
            columns = IOS_APP_COLUMNS
            args = ["-l"]
        _, out = await sh("ideviceinstaller", "-u", self.serial, *args, timeout=90)
        # "com.foo.bar, "1.0", "Foo"" — the quotes are the tool's own, and the
        # first line it prints is the column names.
        found: set[str] = set()
        self.executables, self.bundles = {}, {}
        for line in out.splitlines():
            row = dict(zip(columns, (p.strip().strip('"') for p in line.split(", "))))
            # is_package drops the tool's own header row along with anything
            # that is not an identifier: neither has a dot in it.
            if not is_package(ident := row.get("CFBundleIdentifier", "")):
                continue
            found.add(ident)
            # The display name is listed and not kept: what an app is called on
            # the home screen is neither what it is installed as nor what its
            # process is called, and a sidebar naming apps one way here and by
            # package on android would be one list read two ways. The two that
            # are used are these — the executable for the pid and the log
            # filter, the bundle path for what is pulled off the phone.
            if executable := row.get("CFBundleExecutable"):
                self.executables[ident] = executable
            # Absolute or nothing: the path is split into `tar -C parent name`,
            # and a relative one would be taken from whatever ssh calls home.
            if (path := row.get("Path", "")).startswith("/"):
                self.bundles[ident] = path
        self.packages = sorted(found)
        if not found:
            self.write("[yellow]no apps listed — check that ideviceinstaller reaches"
                       f" the phone: {escape(last_line(out)) or 'it said nothing'}")

    async def stats(self) -> dict[str, str]:
        # The battery comes over usbmux, so it is there even with ssh down —
        # but it is a fresh connection to the phone every time, for a number
        # that moves by the minute. Asked once every BATTERY_TICKS polls and
        # kept in between, which is the difference between one round trip per
        # three seconds and one per half minute.
        if self._batt_due <= 0:
            _, batt = await sh("ideviceinfo", "-u", self.serial, "-q",
                               "com.apple.mobile.battery",
                               "-k", "BatteryCurrentCapacity", timeout=10)
            self._batt = next((tok for tok in batt.split() if tok.isdigit()), "?")
            self._batt_due = BATTERY_TICKS
        self._batt_due -= 1
        # The marker with nothing behind it once the phone has said it has
        # none of these: the four that follow are four failed execs on the
        # phone every three seconds, and the section still has to be there —
        # its absence is what tells address() the batch never ran at all.
        probe = ("echo @ip;" if self._no_ip_tool else
                 "echo @ip; ipconfig getifaddr en0 || ifconfig -a"
                 " || scutil --nwi || netstat -in;")
        batch = ("echo @load; sysctl -n vm.loadavg;"
                 "echo @mem; sysctl -n hw.memsize; vm_stat;"
                 # Four tries in that probe, because none of them is on
                 # every phone: ipconfig answers with the address alone,
                 # ifconfig with every interface — cellular is pdp_ip0, and
                 # the loopback it lists first is dropped by the pattern in
                 # address() — while scutil and netstat are what is left on a
                 # phone that has neither. A phone with none of the four is
                 # answered from this machine's arp table instead: see
                 # wifi_address(). Unfiltered on purpose: piping any of them
                 # into grep found nothing at all on a phone that has no grep,
                 # which is most of them.
                 + probe +
                 f"echo @ps; {self.frida_ps};")
        _, out = await self.run(batch, root=False)
        s = sections(out)
        # An ssh that never opened reads exactly like a phone whose sysctl is
        # not on the PATH; both come back here as nothing arriving. The marker
        # and not the exit status, for the reason the android side gives.
        self.say_stats("load" in s, out, "over ssh")
        return {
            "batt": self._batt,
            "load": first(s, "load", r"([\d.]+)") or "?",
            "mem": ios_memory(s.get("mem", [])),
            "ip": await self.address(s),
            "frida": self.frida_in(s.get("ps", [])) or "",
            # iOS runs an app as the executable inside its bundle, not as its
            # bundle id: the name is resolved once in package_chosen(), and the
            # process table already fetched above carries its full path.
            "pid": pid_of(s.get("ps", []), self.proc_name) or "-",
        }

    async def address(self, s: dict[str, list[str]]) -> str:
        """What the stats line's address row says, in four falling steps.

        The phone's own answer; failing that the host this panel reaches it on,
        which is the phone's address when it is not the tunnel's loopback;
        failing that this machine's arp table; and failing all of those `usb`,
        because a phone on the end of a cable with nothing on the network has
        no address to show — which is worth the row more than a dash is. `?`
        stays for the reading that never happened at all.
        """
        # The phone's own answer: any address but the loopback, out of a bare
        # ipconfig line, a whole ifconfig dump, scutil's summary or netstat's
        # table.
        mine = first(s, "ip", r"\b(?!127\.)(\d{1,3}(?:\.\d{1,3}){3})\b")
        said = " ".join(ln.strip() for ln in s.get("ip", []) if ln.strip())
        # A phone either has one of those commands or it does not, so once it
        # has said which, the answer is kept for as long as the panel is open —
        # and the probe stops being sent with it. Closing the panel is what
        # asks again, which is the right price: four failed execs every three
        # seconds against a reading that does not change on a given phone.
        #
        # ssh folds the far end's stderr into whichever section is open when
        # it lands, so the saying itself comes and goes from one poll to the
        # next even though the phone does not — and reading each poll on its
        # own put this line in the log every few seconds and flickered the row
        # between an address and `usb`.
        if not_there(said):
            self._no_ip_tool = True
        if mine:
            self._no_ip_tool = False
            return mine
        # Only if the batch ran: with ssh down, naming the address the panel
        # was pointed at would be the one row claiming to know something while
        # every other one says ?.
        if "ip" not in s:
            return "?"
        if self.ssh_host != "127.0.0.1":
            return self.ssh_host
        # Only when the phone has said it has no such command. An empty section
        # means one of them ran and found no address, and the arp table would
        # answer that with a stale entry from when the phone was last on the
        # network.
        if self._no_ip_tool:
            # Once every BATTERY_TICKS polls, like the battery: an arp lookup
            # is local and cheap, but not three seconds' worth of cheap.
            if self._arp_due <= 0:
                self._arp, self._arp_due = await self.wifi_address() or "", BATTERY_TICKS
            self._arp_due -= 1
            if self._arp:
                return self._arp
        # `usb` and nothing said. The phone is on the end of a cable, usbmux
        # carries no address of its own — lockdownd hands out the wifi MAC and
        # never the lease — and which of ipconfig, ifconfig, scutil and netstat
        # this jailbreak left out is not something anybody can act on. The row
        # says what there is, which is the cable; u points the panel at the
        # phone by address instead, and the readme says so.
        return "usb"

    async def wifi_address(self) -> str | None:
        """The phone's address off this machine's arp table, by its wifi MAC.

        A phone with none of ipconfig, ifconfig, scutil or netstat on it can
        still be found from here, as long as the two are on the same network
        and have spoken: lockdownd hands out the wifi MAC over usbmux, and the
        arp table maps that to the address the router gave the phone.

        `ip neigh` first because arp is deprecated on linux and missing on
        some distributions; arp is what answers on macOS.
        """
        if not (mac := self.props.get("WiFiAddress", "")):
            return None
        want = mac_key(mac)
        _, out = await sh("sh", "-c", "ip neigh show 2>/dev/null || arp -an", timeout=5)
        for line in out.splitlines():
            if not any(want == mac_key(tok) for tok in line.split() if tok.count(":") == 5):
                continue
            if m := re.search(r"\b(\d{1,3}(?:\.\d{1,3}){3})\b", line):
                return m.group(1)
        return None

    async def package_chosen(self) -> None:
        """Find the executable the app runs as, for the pid in the stats line.

        Off the app list where the installer gave it, which is instant and
        needs nothing on the phone. Failing that the glob grep behind
        bundle_dir(), which takes seconds on a phone with a few hundred apps —
        fine once when the app is picked, hopeless in a poll that runs every
        three seconds.
        """
        self._proc_for = self.package or ""
        if executable := self.executables.get(self.package or ""):
            self.proc_name = executable
            return
        bundle = await self.bundle_dir() if self.package else ""
        self.proc_name = bundle.rsplit("/", 1)[-1].removesuffix(".app") if bundle else ""
        if self.package and not self.proc_name:
            self.write(f"[yellow]{escape(self.package)}: no bundle on this phone"
                       " — no pid and no log filter; pick it again to look once more")

    async def system_info(self) -> None:
        self.write(f"[b]system  {escape(self.serial)}[/]")
        for key in ("DeviceName", "ProductType", "ProductVersion", "BuildVersion",
                    "CPUArchitecture", "SerialNumber", "WiFiAddress", "TimeZone"):
            # Padded past the longest key there is, and a space after it:
            # cpuarchitecture is fifteen characters, so a narrower column ran
            # every name straight into its own value.
            self.write(f"  [b]{key.lower():<15}[/] {escape(self.props.get(key, '-'))}")
        # No screen row to match the android dump's: lockdownd has no
        # dependable key for the display size across versions, and a guess in a
        # summary of what the device is would be worse than its absence.
        batch = ("echo @kernel; uname -a;"
                 "echo @uptime; uptime;"
                 "echo @storage; df -h / /var;"
                 # ipconfig alone, unlike the four the stats line falls
                 # through: an `ifconfig -a` dump is forty lines, and
                 # dump_sections puts a row on one. A phone without it reads
                 # `-`, which is what every other row here does for a command
                 # the device has not got.
                 "echo @net; ipconfig getifaddr en0;"
                 "echo @jailbreak; ls -d /var/jb /Applications/Sileo.app"
                 " /Applications/Cydia.app /var/jb/Applications/Sileo.app 2>/dev/null;"
                 "echo @dpkg; command -v dpkg apt;"
                 f"echo @ps; {self.frida_ps};")
        _, out = await self.run(batch, timeout=30, root=False)
        # Fifteen, the width the lockdownd keys above are padded to: one dump,
        # one column, whichever half of it a row came from.
        self.dump_sections(sections(out), 15)
        # The same shape as the android dump's root row: what it is, then
        # whether that reaches root.
        self.write(f"  [b]{'ssh':<15}[/] "
                   f"{escape(f'{self.ssh_user}@{self.ssh_host}:{self.ssh_port}')}"
                   + ("  [green]root: yes[/]" if self.root else "  [red]root: no[/]"))

    async def frida_blocker(self) -> str | None:
        if self.root:
            return None
        return (f"frida-server needs root, and {self.ssh_user}@{self.ssh_host} has none"
                " — u sets which account to log in as; mobile needs sudo on the phone")

    async def install(self, path: str) -> tuple[int, str]:
        args = ["ideviceinstaller", "-u", self.serial,
                *(["install", path] if await installer_takes_commands() else ["-i", path])]
        self.write(f"[dim]$ {shlex.join(args)}")
        rc, out = await sh(*args, timeout=900)
        # ideviceinstaller says "Install: Complete" and means it; anything else
        # with a zero status is a refusal it printed on the way out.
        if rc == 0 and "Complete" not in out:
            rc = 1
        # The two refusals every unsigned ipa gets. Nothing here can sign an
        # app — that needs a certificate — so the fix is on the phone, and it
        # is worth naming rather than leaving as an error code.
        if ("ApplicationVerificationFailed" in out
                or "MismatchedApplicationIdentifierEntitlement" in out):
            out += ("\n  the ipa is not signed for this device: install AppSync Unified"
                    " on the phone, or sign the ipa first")
        elif "iTunesMetadata" in out:
            out += ("\n  the ipa has no iTunesMetadata.plist — one repacked off a device"
                    " never does; AppSync Unified installs it anyway")
        return rc, out.strip() or ("ideviceinstaller failed" if rc else "installed")

    async def existing_exports(self, dest: str) -> list[Path]:
        """Paths of any ipa files that already exist in dest."""
        ipa = Path(dest) / f"{self.package or 'app'}.ipa"
        return [ipa] if ipa.exists() else []

    async def save_app(self, dest: str) -> None:
        """Copy the installed bundle off the phone and repack it as an ipa.

        An ipa is a zip with the bundle under Payload/, which is why the copy
        goes into a directory of that name and the whole thing is zipped on
        the host — no zip, tar or free space needed on the phone. The binary
        inside is still FairPlay-encrypted unless the app was decrypted on the
        device, which is what frida-ios-dump and bagbak are for.
        """
        if not (bundle := await self.bundle_dir()):
            self.fail(f"{self.package}: no bundle on this phone under"
                      " /var/containers/Bundle/Application or /Applications")
            return
        try:
            staged = Path(tempfile.mkdtemp(prefix="moabile-ipa-"))
            payload = staged / "Payload"
            payload.mkdir()
        except OSError as exc:              # no room, or nowhere to write
            self.fail(f"nowhere to stage {self.package}: {exc.strerror or exc}")
            return
        try:
            rc, out = await self.pull(bundle, str(payload))
            if rc != 0:
                self.fail(out)
                return
            base = str(Path(dest) / (self.package or "app"))
            ipa = Path(f"{base}.ipa")
            self.write(f"zip     {escape(bundle)} -> [b]{ipa}[/]")
            try:
                # In a thread: zipping a few hundred megabytes on the event
                # loop freezes every panel until it finishes. Beside the
                # destination rather than in /tmp, so the rename below stays
                # on one filesystem and cannot half-copy.
                zipped = await asyncio.to_thread(shutil.make_archive, base, "zip", str(staged))
            except OSError as exc:              # no room, or nowhere to write
                # Half an archive in the directory the user picked is worse
                # than none: it looks like an ipa and is not one.
                Path(f"{base}.zip").unlink(missing_ok=True)
                self.fail(f"{base}.zip: {exc.strerror or exc}")
                return
            Path(zipped).replace(ipa)
            self.write(f"saved   {ipa} ({ipa.stat().st_size // 1024} KiB)"
                       " [dim]— binary still encrypted unless the app was decrypted[/]")
        finally:
            # In a thread like the zip above: a staged bundle is the whole app,
            # and unlinking a few hundred megabytes of it on the event loop
            # freezes every panel for as long as it takes.
            await asyncio.to_thread(shutil.rmtree, staged, ignore_errors=True)

    async def shell_argv(self) -> tuple[list[str], str]:
        """An ssh session in the pane, password prompt and all.

        batch=False here alone among the commands: the master is brought up
        first so there is normally nothing to answer, but if it could not be
        opened this is the one place a prompt can still be typed into.
        """
        await self.master_up()
        return (self.ssh_argv(batch=False),
                f"ssh -p {self.ssh_port} {self.ssh_user}@{self.ssh_host}")

    async def set_login(self) -> None:
        """Ask which account reaches this phone.

        A jailbreak usually refuses root over ssh and leaves only `mobile`,
        whose password is the one every jailbreak ships with — so that is what
        this starts from. Nothing is installed on the phone to make it easier:
        the password opens one connection, the rest ride it, and sudo covers
        what mobile cannot reach on its own.
        """
        was = f"{self.ssh_user}@{self.ssh_host}:{self.ssh_port or IOS_SSH_PORT}"
        answer = await self.mob.push_screen_wait(AskScreen(
            f"ssh login for {self.serial}", was,
            "user@host:port — 127.0.0.1 goes down the usb tunnel, any other host over"
            " the network. mobile is the account most jailbreaks leave open; root"
            " is usually refused, and sudo covers the difference."))
        if not (answer := (answer or "").strip()):
            return
        user, _, rest = answer.partition("@")
        host, _, port = rest.rpartition(":")
        # No slash anywhere in it: the host goes into the name of the control
        # socket under the temporary directory, and one with a slash in it is
        # a path that does not exist — which ssh reports as a connection that
        # failed rather than as the address being nonsense.
        if not (user and host and port.isdigit()) or "/" in answer:
            self.fail(f"{answer}: expected user@host:port")
            return
        # The tunnel and the multiplexed master belong to the old login.
        await self.drop_tunnel()
        self.ssh_user, self.ssh_host, self.ssh_port = user, host, int(port)
        self.write(f"ssh login [b]{self.ssh_user}@{self.ssh_host}:{self.ssh_port}[/]"
                   + ("" if user == "root" else "  [dim]— commands go through sudo[/]"))
        # A login this panel has not used yet starts from the default again,
        # and nothing said about the last one is news held over this one.
        self.password, self.master_said = IOS_DEFAULT_PASSWORD, False
        self.say_again()
        await self.load()

    def mirror_argv(self, index: int) -> list[str]:
        # ioscpy has no geometry flags, so unlike scrcpy the windows are not
        # tiled: it opens where it opens.
        return ["ioscpy", "--device", self.serial]

    async def log_command(self, pid: str) -> list[str]:
        """idevicesyslog, whole, with the pid applied on this side of the cable.

        The tool's own filter is `-p`, and it matches process *names*: a
        second process called something similar comes with it, and the name is
        not the bundle id either — an app shown as "My App" runs as MyApp. So
        it is not used at all. Every line carries the pid in brackets right
        after the process name, and the panel keeps the lines holding `[pid]`
        and drops the rest. The bracket anchors it: [4600] is not [14600].
        """
        self.log_keep = f"[{pid}]" if pid else ""
        # MASTG-TECH-0060: idevicesyslog is a system log collector, and debug
        # and info level entries from the unified log may never reach it.
        self.write("[dim]syslog carries what reaches the unified log:"
                   " debug and info entries may be missing[/]")
        return ["idevicesyslog", "-u", self.serial]

    async def app_pid(self) -> str | None:
        """Whether the selected app is running, and as which pid.

        The process table, like the stats line — where this used to be
        `frida-ps -a`, which is a python program that cannot answer at all
        until frida-server is up, and this question is asked before it is.
        """
        if self._proc_for != (self.package or ""):
            await self.package_chosen()
        _, out = await self.run(IOS_PS, root=False)
        return pid_of(out.splitlines(), self.proc_name)

    async def server_bytes(self) -> int | None:
        """The server's size, but only with the agent there beside it.

        frida-server loads the agent from a fixed path next to itself and is
        inert without it: a binary on its own would come up, hold the port and
        fail to inject into anything, with nothing saying why. So it is
        reported as nothing there at all, which pushes both files rather than
        offering to start half an installation.
        """
        size = await super().server_bytes()
        if size is None:
            return None
        rc, _ = await self.run(f"[ -f {self.server_junk}/frida-agent.dylib ]")
        return size if rc == 0 else None

    async def server_files(self, ver: str, arch: str) -> list[tuple[Path, str]] | None:
        """The two files out of frida's iOS package, unpacked on the host.

        There has been no `frida-server-<ver>-ios-<arch>.xz` for some time —
        asking for one is a 404 — and the .deb that replaced it is not just a
        rename: frida-server loads its agent from a fixed path beside it, so
        pushing the server on its own gets a process that starts and then
        cannot inject into anything.

        The package is built for a rootless jailbreak, with everything under
        /var/jb. On a rootful one that prefix is stripped, which is the same
        `jb` the rest of this class already keys off.
        """
        self.prune_cache(ver)
        deb = CACHE / f"frida_{ver}_{self.frida_platform}-{arch}.deb"
        unpacked = CACHE / f"frida-{ver}-{self.frida_platform}-{arch}"
        if not unpacked.is_dir():
            fresh = deb.exists() and deb.stat().st_size >= MIN_SERVER_BYTES
            if not fresh and not await self.download(
                    f"{FRIDA_RELEASES}/{ver}/frida_{ver}_{self.frida_platform}-{arch}.deb", deb):
                return None
            try:
                inside = await asyncio.to_thread(unpack_deb, deb, unpacked)
            except (OSError, ValueError, tarfile.TarError) as exc:
                shutil.rmtree(unpacked, ignore_errors=True)
                deb.unlink(missing_ok=True)
                self.fail(f"{deb.name}: {exc}")
                return None
            self.write(f"unpack  {len(inside)} files from [b]{deb.name}[/]")
        else:
            self.write(f"cached  [b]{unpacked}[/]")
        payload = []
        for path in IOS_FRIDA_FILES:
            local = unpacked.joinpath(*path.lstrip("/").split("/"))
            if not local.is_file():
                self.fail(f"{deb.name} did not contain {path}")
                return None
            payload.append((local, f"{self.jb}{path.removeprefix('/var/jb')}"))
        return payload

    async def dir_holding(self, plists: str) -> str:
        """The directory of the first plist naming the selected package, or "".

        grep, not a plist parser: the identifier sits as a plain string inside
        a binary Info.plist, and this is one command instead of a download and
        a parse per installed app. It is also the one thing here that needs
        grep on the phone, and a phone that has not got it would otherwise
        answer exactly like one where the app is not installed.
        """
        rc, out = await self.run(
            f"grep -ls {shlex.quote(self.package or '')} {plists} 2>/dev/null",
            timeout=120, root=False)
        found = [ln.strip() for ln in out.splitlines() if ln.strip().endswith(".plist")]
        # grep is the one thing here that has to be on the phone, and a
        # jailbreak that left it out cannot be told from an app that is not
        # installed unless this is said. Once, and in our own words: what the
        # shell called it is not the point.
        #
        # The status and not only the words: the 2>/dev/null above is there for
        # the globs that match nothing, and it takes the shell's own "not
        # found" with them — so on most phones the only thing left saying which
        # of the two happened is the 127 every shell exits with for a command
        # it could not run.
        if not found and (rc == 127 or not_there(out)):
            self.say_once("grep", "no grep on the phone: an app's bundle and data"
                          " directory cannot be searched for", quiet=True)
        elif not found and rc != 0 and out.strip():
            self.write(f"[yellow]{escape(out.strip()[:120])}")
        return found[0].rsplit("/", 1)[0] if found else ""

    async def bundle_dir(self) -> str:
        """The .app the selected package was installed as, or "" if not found.

        The app list carries it where the installer is new enough to be asked
        (see load_packages); the search below is for where it is not. Both
        places an app can live — /var/containers for anything installed,
        /Applications for the system ones and whatever the jailbreak put there.
        """
        if path := self.bundles.get(self.package or ""):
            return path
        return await self.dir_holding(
            "/var/containers/Bundle/Application/*/*.app/Info.plist"
            " /Applications/*.app/Info.plist"
            # Only where it is a second place to look: on a rootful jailbreak
            # jb is empty and this is the line above written twice, which is
            # one more sweep of every Info.plist on the phone for nothing.
            + (f" {self.jb}/Applications/*.app/Info.plist" if self.jb else ""))

    async def data_dir(self) -> str:
        """The app's Data container, which is not the bundle it was installed from.

        An iOS app has two containers with two different UUIDs — MASTG-TECH-0059
        — and only the second holds Documents, Library and the databases. The
        guide reads the pair out of `ipainstaller -i`, which is one more thing
        that has to be on the phone; every Data container instead carries a
        metadata plist with the bundle id inside it, so it can be found the
        same way the bundle already is.
        """
        return await self.dir_holding(
            "/var/mobile/Containers/Data/Application/*/"
            ".com.apple.mobile_container_manager.metadata.plist")

    async def wake_app(self) -> None:
        """Bring the app to the front before anything attaches to it.

        iOS suspends an app that is not on screen. It is still in the process
        table, so a pid is found and objection or frida is handed one — and
        then nothing happens at all, because a suspended process runs no code
        to attach to. It came alive the moment the app was opened by hand,
        which read as a hang up until then.

        open(1) on an app that is already up foregrounds it and keeps its
        state, so this is the same call that starts one, and where the phone
        has it there is nothing to say. Where it has not, the app stays off
        screen and the only way through is the phone itself — one line, in the
        log the pane runs underneath rather than over.
        """
        if not await self.launch_app():
            self.write(f"[yellow]open {escape(self.package or '')} on the phone:"
                       " a suspended app has nothing running to attach to")

    async def launch_app(self) -> bool:
        """Start the app with open(1), as the login user before as root.

        open(1) is uikittools', which the jailbreak package managers ship. It
        asks SpringBoard to launch the app, and SpringBoard is mobile's — so
        asking through sudo is asking from outside the session that owns the
        screen, which is how this came back as a success that launched nothing
        and left objection with no process to attach to. The login user first,
        the way the rest of this class asks for root only where root is what
        is needed; sudo second, for a phone that keeps open where mobile
        cannot reach it.

        And what open said, either way it went — except the one thing it can
        say that is not about this app at all. A phone without uikittools has
        no open to run, and "sh: open: not found" is neither a failure of the
        app nor anything to fix: there is no other way to launch one from
        here, so it comes back as False and the caller asks for the app to be
        opened on the phone instead. See not_there().
        """
        target = shlex.quote(self.package or "")
        rc, out = await self.run(f"open {target}", root=False)
        if rc == 0:
            return True
        # The status as well as the words, the same pair dir_holding reads: a
        # shell that has no open exits 127 whatever it words the message as,
        # and every one of them words it differently.
        if rc == 127 or not_there(out):
            return False
        self.write(f"[yellow]open {escape(self.package or '')}:"
                   f" {escape(last_line(out)) or f'exited {rc}'}")
        if self.ssh_user == "root":
            return False
        rc, out = await self.run(f"open {target}")
        if rc == 0:
            return True
        if rc != 127 and not not_there(out):
            self.write(f"[yellow]sudo open: {escape(last_line(out)) or f'exited {rc}'}")
        return False


class MOABile(App):
    CSS = """
    #body { height: 1fr; }
    #side { width: 34; border-right: solid $panel; }
    /* The apps of the active device sit at the foot of the sidebar rather than
       flush under the device rows: the two lists answer different questions,
       and stacked together the second one read as more of the first. The
       ceiling is what keeps a long app list from squeezing the devices off
       the top. */
    #apps { dock: bottom; height: auto; max-height: 60%; }
    /* Past the twelve rows every other list here stops at: the app list is
       the one with hundreds of entries behind it, and the block above already
       caps it at a share of the sidebar. */
    #packages { max-height: 100%; }
    /* Which device the keys are about. Several panels can be open at once and
       only one of them is listening, so the row for it carries the same accent
       as the border of the panel itself. The weight and the colour and not a
       ground of its own: the list's cursor is already a band of background,
       and a second one beside it reads as two cursors. */
    ListItem { background: transparent; color: $foreground; padding: 0 1; }
    ListItem:hover { background: $panel; color: $foreground; }
    ListItem.-highlight, ListItem.-selected { background: $panel; color: $foreground; }
    ListView:focus > ListItem.-highlight,
    ListView:focus > ListItem.-selected { background: $accent; color: $background; }
    ListView:focus > ListItem.-highlight Label,
    ListView:focus > ListItem.-selected Label { color: $background; text-style: bold; }
    ListItem.-dir Label { color: $primary; text-style: bold; }
    ListView:focus > ListItem.-highlight.-dir Label,
    ListView:focus > ListItem.-selected.-dir Label { color: $background; text-style: bold; }
    #devices > .-active Label, #packages > .-active Label { color: $accent; text-style: bold; }
    ListView:focus > #devices > .-active.-highlight Label,
    ListView:focus > #devices > .-active.-selected Label,
    ListView:focus > #packages > .-active.-highlight Label,
    ListView:focus > #packages > .-active.-selected Label { color: $background; text-style: bold; }
    #panels { width: 1fr; overflow-x: auto; scrollbar-size-horizontal: 1; }
    /* 1fr each, so two devices attached are two panels side by side rather
       than one filling the row. The padding lives on the children: on the
       panel itself it would hold the rule above a running tool a column short
       of each border. */
    .panel { width: 1fr; min-width: 40; border: round $panel; padding: 0; }
    .panel > Static, .panel > RichLog, .panel > TerminalPane { padding: 0 1; }
    .panel:focus, .panel:focus-within { border: round $accent; }
    #empty { width: 1fr; height: 1fr; content-align: center middle; color: $text-muted; }
    .head { background: $panel; color: $text-muted; padding: 0 1; }
    TerminalPane { height: 0; }
    .running TerminalPane { height: 1fr; border-top: solid $accent; }
    RichLog { height: 1fr; }
    ListView { height: auto; max-height: 12; }
    /* Borderless and one row tall: Textual's Input is three rows by default,
       and the two blank ones read as a gap between the field and whatever it
       filters. $panel and not $boost, here and in the file browser: boost is
       transparent in any theme that names its own panel colour — which both of
       these do — so the field had no ground at all and read as a stray line of
       text. */
    Input { border: none; height: 1; background: $panel; }
    /* The bottom row: a pinned key at each end and the scrolling bar between
       them. dock: none because Footer docks itself to the bottom by default,
       which inside the row would lay it over both. */
    #bar { dock: bottom; height: 1; background: $footer-background; }
    #bar Footer { dock: none; width: 1fr; }
    BarKey { width: auto; height: 1; padding: 0 1; background: $footer-item-background; }
    BarKey:hover { background: $block-hover-background; }
    """

    # The bar has room for a word each; the tooltip is where the whole
    # sentence lives, and it is what hovering a key and the h panel show.
    BINDINGS: ClassVar[list[BindingType]] = [
        Binding("r", "rescan", "rescan", tooltip="look for attached devices again"),
        # show=False for the two pinned to the ends of the bottom row: the
        # bar would otherwise carry a second copy of each. The help panel
        # lists them either way — it hides only Textual's own bindings.
        Binding("b", "panel", "sidebar", show=False,
                tooltip="hide or show the sidebar of devices and apps"),
        Binding("f", "frida_server", "frida",
                tooltip="start frida-server on the device, installing it first, or stop it"),
        Binding("s", "frida_client", "spawn",
                tooltip="run frida against the selected app with arguments you pick"
                        " — spawned, or attached to where it is already running"),
        Binding("o", "objection", "objection",
                tooltip="start the app if needed and explore it with objection"),
        Binding("w", "mirror", "window",
                tooltip="mirror the screen in a window of its own"
                        " — scrcpy on android, ioscpy on ios"),
        Binding("t", "shell", "terminal",
                tooltip="open a shell on the device in this panel — su over adb, or ssh"),
        Binding("l", "log", "log",
                tooltip="stream logcat or the ios syslog into the panel,"
                        " whole or filtered to the app"),
        Binding("d", "files", "files",
                tooltip="browse the device and the host side by side, and push or pull files"),
        Binding("a", "install", "add",
                tooltip="install an apk or ipa picked off the host"),
        Binding("e", "save_app", "export",
                tooltip="save the selected app's apk or ipa into a host directory you pick"),
        Binding("i", "info", "info",
                tooltip="dump what the device is — build, kernel, storage, network,"
                        " and its root or jailbreak state"),
        Binding("u", "login", "user",
                tooltip="set which account, host and port reach this device over ssh"),
        Binding("p", "frida_purge", "purge",
                tooltip="stop frida-server and delete it from the device, leaving nothing behind"),
        Binding("k", "clean", "clear", tooltip="empty this panel's log"),
        Binding("v", "screenshot", "svg", tooltip="save an SVG of this interface"),
        Binding("m", "theme", "mode", tooltip="switch between the dark and the light mode"),
        Binding("h", "keys", "help", show=False,
                tooltip="show or hide the key and widget help panel"),
        Binding("q", "quit", "quit", tooltip="stop everything this app started and exit"),
    ]
    # A key is the first letter of the word beside it in the bar wherever the
    # letter was free — the bar is where a command is found, and a key standing
    # for nothing in it has to be memorised twice. Three of them could not have
    # their own letter: b for the sidebar (its bar), v for svg, and d for files,
    # which is the directory key every file manager has. k for clear is the one
    # plain convention, the way it clears a line in a shell.
    #
    # All nineteen need about 155 columns, so a narrower terminal shows the
    # front of the bar and h opens the panel with the rest — which is why h is
    # pinned to the end of the row instead of scrolling with the seventeen it
    # is there to recover. The help panel lists it and b either way: it drops
    # Textual's own bindings and keeps ours, shown in the bar or not.
    # No command palette: every command is a key in the bar below, and a
    # second list of the same commands was one surface too many.
    ENABLE_COMMAND_PALETTE = False

    def __init__(self) -> None:
        super().__init__()
        self.serials: list[str] = []
        # Which device families the installed tools can drive at all, and what
        # each attached serial turned out to be.
        self.ready: list[str] = []
        self.kinds: dict[str, str] = {}
        # Attached, but not answering yet: (serial, what adb calls it).
        self.waiting: list[tuple[str, str]] = []
        self._active: DevicePanel | None = None
        self._ticking = False
        # What the package list is currently showing, and the pending redraw
        # of it: see show_packages().
        self._drawn: tuple = ()
        self._filtering: Timer | None = None

    def compose(self) -> ComposeResult:
        yield Header()
        with Horizontal(id="body"):
            with Vertical(id="side"):
                # The name where it stays put, with what it stands for: the header
                # carries the name too, but that line is mostly the active panel's
                # serial. It fits the 34 columns the sidebar has, which is why
                # "devices" gives way — the rows under it are the devices, and the
                # empty panel is where "enter toggles" is said at more length.
                yield Static("MOABile · mother of all mobile", classes="head")
                yield ListView(id="devices")
                # At the foot of the sidebar, not under the devices: the apps
                # belong to whichever device is marked active above, and the
                # gap between the two lists is what says so.
                with Vertical(id="apps"):
                    yield Static("apps", classes="head", id="pkghead")
                    yield Input(placeholder="filter…", id="filter")
                    yield ListView(id="packages")
            with HorizontalScroll(id="panels"):
                yield Static(id="empty")
        with Horizontal(id="bar"):
            yield self.bar_key("b")
            # compact: the bar is the only list of commands there is, so fitting
            # as many of them on one line as possible is the whole job.
            yield Footer(compact=True)
            yield self.bar_key("h")

    def notify(self, message: str, *, title: str = "",
               severity: SeverityLevel = "information",
               timeout: float | None = None, markup: bool = False) -> None:
        """Every toast in here is plain text, and markup is dropped whatever
        was asked for.

        Half of these messages are device output — what adb said about a
        refused push, what the phone said about sudo — and Textual parses a
        notification as markup by default. One `[/]` in a line off the phone
        was then a MarkupError raised inside the toast's own render, which
        takes the whole app down: no panel to write it to, no way back.

        Overridden here rather than passed at each call because Widget.notify
        forwards its own `markup=True` down to this, so every notification
        raised from a modal came with it on regardless of the default. The
        same reasoning as RichLog(markup=False) and the escape() on every
        Static.update() in here — this was the one surface still parsing it.
        """
        super().notify(message, title=title, severity=severity,
                       timeout=timeout, markup=False)

    def bar_key(self, key: str) -> BarKey:
        """The pinned copy of a key, worded by the binding it stands for."""
        # isinstance: a BINDINGS list is allowed to hold plain tuples, and a
        # tuple has no tooltip to read.
        binding = next(b for b in self.BINDINGS if isinstance(b, Binding) and b.key == key)
        return BarKey(key, binding.description, binding.tooltip)

    def on_mount(self) -> None:
        # The one place the capitals survive: paths and the command are all
        # lowercase, and the header is where the name is actually read.
        self.title = "MOABile"
        # Two themes, both readable. The rest are variations on the same two
        # and only make the mode command a list to scroll.
        self.register_theme(DARK)
        self.register_theme(LIGHT)
        # Only if both are still there: a Textual that renames its built-ins
        # would otherwise leave this app with no theme at all.
        if all(name in self.available_themes for name in KEEP_THEMES):
            for name in list(self.available_themes):
                if name not in KEEP_THEMES:
                    self.unregister_theme(name)
            self.theme = KEEP_THEMES[0]
        self.startup()

    @work
    async def startup(self) -> None:
        # Only where it fits: the alternative is a logo with its head cut off,
        # in front of the screen that says what is missing.
        if self.size.height >= LOGO_ROWS + 4 and self.size.width >= LOGO_COLS + 4:
            await self.push_screen_wait(LogoScreen())
        # Checking the tools serially blocked the UI for seconds; objection
        # alone takes over a second just to import.
        while True:
            gate = DepsScreen(await self.check_deps())
            answer = await self.push_screen_wait(gate)
            if answer == "quit":
                self.exit()
                return
            if answer == "go":
                # Only the complete families are looked for: half a toolchain
                # finds devices it then cannot do anything with.
                self.ready = gate.ready
                break
        await self.refresh_devices(auto_open=True)
        self.set_interval(3, self.tick)

    async def check_deps(self) -> list[Tool]:
        async def one(tool: Tool) -> Tool:
            if not shutil.which(tool.name):
                return tool
            _, out = await sh(tool.name, tool.flag, timeout=5)
            # The number and nothing else: every one of these answers with its
            # own name, a usage line or a URL around it, and none of that is
            # news on a screen that already lists the names.
            found = re.search(r"\d+(?:\.\d+)+", out)
            if not found:
                # ssh answers --version with "unknown option" and its usage:
                # the number is behind -V, which is its own spelling of it.
                # Left as a fallback rather than a flag of its own, for the
                # tools whose spelling nobody here has had in their hands.
                _, out = await sh(tool.name, "-V", timeout=5)
                found = re.search(r"\d+(?:\.\d+)+", out)
            return tool._replace(version=found.group() if found else "installed", present=True)

        return list(await asyncio.gather(*(one(t) for t in DEPS)))

    # ---------------------------------------------------------------- panels

    @property
    def panels(self) -> list[DevicePanel]:
        return list(self.query(DevicePanel))

    @property
    def active(self) -> DevicePanel | None:
        """Panel that keystrokes and sidebar choices apply to.

        Tracked explicitly rather than derived from focus: the sidebar lives
        outside every panel, so as soon as its list or filter took focus a
        focus-derived lookup fell back to the first panel and applied every
        selection to the wrong device.
        """
        panels = self.panels
        if self._active in panels:
            return self._active
        return panels[0] if panels else None

    def keep_focus_alive(self) -> None:
        """Take the keyboard back from a widget that is no longer mounted.

        A closed or unplugged panel keeps the focus it had, and every key then
        goes to a widget that is not on screen — the app looks dead until you
        click something.
        """
        # is_attached, not is_mounted: a removed widget still answers True to
        # the second one, and every key went on reaching it.
        if (focused := self.focused) is not None and not focused.is_attached:
            self.set_focus(self.active)

    def panel(self, serial: str) -> DevicePanel | None:
        return next((p for p in self.panels if p.serial == serial), None)

    def target(self) -> DevicePanel | None:
        """The panel an action applies to, or a visible complaint."""
        if (panel := self.active) is None:
            self.notify("no device panel open · enter on a device", severity="warning")
        return panel

    def on_descendant_focus(self, event: events.DescendantFocus) -> None:
        """Focus anywhere inside a panel makes it active; the sidebar leaves it alone."""
        node: object = event.widget
        while node is not None:
            if isinstance(node, DevicePanel):
                if node is not self._active:
                    self._active = node
                    self.sync_sidebar()
                return
            node = getattr(node, "parent", None)

    def tick(self) -> None:
        """Timer callback: hand the polling to a worker and return at once.

        Textual dispatches a node's messages one at a time, so awaiting adb here
        would stall every other message the App has to handle — which is exactly
        how the interface used to seize up after a while.
        """
        self.poll()

    @work(group="poll")
    async def poll(self) -> None:
        # One poll at a time. When adb is slow the timer keeps firing, and the
        # overlapping polls pile up until the interface stops responding.
        if self._ticking:
            return
        self._ticking = True
        try:
            await self.refresh_devices()
            # Concurrently: serial refreshes made each extra device add its own
            # round-trip delay to every tick.
            # return_exceptions: one device failing must not stop the others.
            await asyncio.gather(*(p.refresh_stats() for p in self.panels),
                                 return_exceptions=True)
        finally:
            self._ticking = False

    def render_device_rows(self) -> None:
        """Redraw the sidebar from known serials. No I/O, so it cannot recurse."""
        lv = self.query_one("#devices", ListView)
        index = lv.index
        lv.clear()
        for serial in self.serials:
            panel = self.panel(serial)
            dot = ("●", "green") if panel else ("○", "dim")
            note = panel.summary() if panel else self.kinds.get(serial, "")
            lv.append(ValueItem(serial, Text.assemble(
                dot, f" {short_serial(serial)}", ("  " + note[:14], "dim") if note else "")))
        for serial, state in self.waiting:
            lv.append(ValueItem(serial, Text.assemble(
                ("✗", "red"), f" {short_serial(serial)}", (f"  {state}", "red"))))
        if index is not None and index < len(self.serials):
            lv.index = index
        self.mark_active()

    def mark_active(self) -> None:
        """Mark the row of the device and package the keys are about.

        A class on the rows already there, not a redraw: the list is rebuilt
        only when what is attached changes, and rebuilding it every time focus
        moved would drop the cursor back to the top the way the package list
        once did.
        """
        panel = self.active
        serial = panel.serial if panel else None
        pkg = panel.package or "" if panel else None
        for row in self.query_one("#devices", ListView).query(ValueItem):
            row.set_class(row.value == serial, "-active")
        for row in self.query_one("#packages", ListView).query(ValueItem):
            row.set_class(row.value == pkg, "-active")

    async def attached(self) -> tuple[dict[str, str], list[tuple[str, str]]]:
        """({serial: family}, [(serial, why it is not usable)]).

        An Android phone whose debugging prompt has not been accepted is listed
        by adb as `unauthorized`, and one still booting as `offline`. Dropping
        those silently is how "nothing is attached" ends up on screen while the
        cable is plainly in. usbmux has no such states — an iPhone that has not
        been trusted is simply listed, and its panel is where that shows up.
        """
        found: dict[str, str] = {}
        waiting: list[tuple[str, str]] = []
        # Together, not one after the other: this runs every three seconds, and
        # usbmux and adb have nothing to say to each other.
        droid, phone = await asyncio.gather(
            sh("adb", "devices") if "android" in self.ready else _nothing(),
            # -l is one udid per line; anything with a space in it is a message.
            sh("idevice_id", "-l") if "ios" in self.ready else _nothing())
        # Only the rows adb separates with a tab. Dropping the first line was
        # not enough: on a cold start adb announces its daemon in two more,
        # sh() folds those in with the rest, and "List of devices attached"
        # itself came back as a device called "List" that was "of".
        rows = [line.split() for line in droid[1].splitlines() if "\t" in line]
        found.update({row[0]: "android" for row in rows if len(row) > 1 and row[1] == "device"})
        waiting += [(row[0], row[1]) for row in rows if len(row) > 1 and row[1] != "device"]
        found.update({ln.strip(): "ios" for ln in phone[1].splitlines()
                      if ln.strip() and " " not in ln.strip()})
        return found, waiting

    async def refresh_devices(self, auto_open: bool = False) -> None:
        """Read what is attached, keeping what is there but not usable too."""
        found, waiting = await self.attached()
        serials = list(found)
        if (serials, waiting) == (self.serials, self.waiting) and not auto_open:
            return
        self.serials, self.waiting, self.kinds = serials, waiting, found
        for p in self.panels:                       # drop panels for unplugged devices
            if p.serial not in serials:
                await p.shutdown()
                await p.remove()
        self.keep_focus_alive()
        # Only on the first pass: otherwise closing the last panel reopens it.
        if auto_open and not self.panels and serials:
            await self.toggle_panel(serials[0])
        self.render_device_rows()
        # The set of devices decides what the middle and the title say, and
        # with nothing attached nothing else was ever going to call this.
        self.sync_sidebar()

    @work(exclusive=True, group="rescan")
    async def action_rescan(self) -> None:
        """Scan for attached devices and refresh package lists on open panels."""
        await self.refresh_devices()
        for p in self.panels:
            await p.load_packages()
        self.sync_sidebar()

    async def toggle_panel(self, serial: str) -> None:
        if state := dict(self.waiting).get(serial):
            self.notify(f"{serial} is {state} — accept the debugging prompt on the device,"
                        " then r", severity="warning")
            return
        if panel := self.panel(serial):
            await panel.shutdown()
            await panel.remove()
            self.keep_focus_alive()
        else:
            family = AndroidPanel if self.kinds.get(serial) == "android" else IosPanel
            panel = family(serial, self)
            await self.query_one("#panels", HorizontalScroll).mount(panel)
            self._active = panel
            panel.focus()
            self.sync_sidebar()
            await panel.load()
        self.sync_sidebar()
        self.render_device_rows()

    def action_panel(self) -> None:
        """Hide the sidebar, handing its columns to the device panels."""
        side = self.query_one("#side")
        side.display = not side.display
        if not side.display:
            # The sidebar must not keep the keyboard while it is invisible:
            # enter and the arrows would go to a list of rows nobody can see.
            # The active panel where there is one — and where there is none,
            # nothing at all, which is what this used to miss: it left focus
            # in the hidden list rather than blurring it. See keep_focus_alive,
            # which does the same for a panel that has gone away.
            self.set_focus(self.active)

    # --------------------------------------------------------------- sidebar

    def sync_sidebar(self) -> None:
        """Point the shared package list at whichever panel is active.

        The title bar names it too: with several panels open, which one the
        keys are about is the thing you have to know at a glance.
        """
        panel = self.active
        # Escaped: the header renders this through Static.update(), which
        # parses markup, and a serial is whatever the tool that listed the
        # device said it was. The package needs none — is_package() has
        # already refused anything with a bracket in it.
        self.sub_title = (f"{escape(panel.serial)} · {panel.package or 'no app'}"
                          if panel else "no device")
        # NoMatches: focus can move — and this runs — before the sidebar is
        # mounted, and a crash there would take the app down at startup.
        with contextlib.suppress(NoMatches):
            empty = self.query_one("#empty", Static)
            empty.display = not self.panels
            if self.serials:
                empty.update("no panel open\n\nenter on a device in the sidebar,"
                             " or [b]r[/] to scan"
                             f"{HELP_HINT}")
            elif self.waiting:
                stuck = ", ".join(f"{serial} is {state}" for serial, state in self.waiting)
                empty.update(f"{escape(stuck)}\n\naccept the debugging prompt on the device,"
                             f" then [b]r[/]{HELP_HINT}")
            else:
                # A family with a tool missing is not scanned at all, so an
                # iPhone in the cable reads as "nothing attached" unless the
                # startup screen is still remembered.
                out = [f for f in FAMILIES if f not in self.ready]
                why = f"\n\n[dim]{', '.join(out)} not scanned: tools missing[/]" if out else ""
                empty.update(f"no device attached\n\nplug one in,"
                             f" then [b]r[/] to scan again{why}{HELP_HINT}")
            self.mark_active()
            self.show_packages(self.query_one("#filter", Input).value)

    def show_packages(self, needle: str, rows: bool = True) -> None:
        """The package count always, and the rows themselves when they changed.

        Every row is a widget mount — a hundred packages take a fifth of a
        second — so a list that is about to come out identical is left alone.
        That is most calls: picking a package redraws the sidebar, and
        rebuilding under the cursor there sent it back to the top of the list.
        """
        panel = self.active
        shown = [p for p in (panel.packages if panel else []) if needle.lower() in p.lower()]
        # The count is the answer to "is my filter too narrow, or is it not
        # installed", which the list alone never gives. It counts every match,
        # not the rows: PACKAGE_ROWS is a ceiling on the drawing, and a head
        # that hid it would read as an app that is not on the device.
        total = len(panel.packages) if panel else 0
        drawing = shown[:PACKAGE_ROWS]
        self.query_one("#pkghead", Static).update(
            f"apps  ·  {len(shown)}/{total}"
            + (f"  ·  {PACKAGE_ROWS} shown" if len(drawing) < len(shown) else "")
            if panel else "apps  ·  no panel"
        )
        if not rows or (drawn := (panel.serial if panel else None, tuple(drawing))) == self._drawn:
            self.mark_active()
            return
        self._drawn = drawn
        lv = self.query_one("#packages", ListView)
        lv.clear()
        # extend, not a loop of append: append mounts one row at a time, and
        # this is one mount for the whole list.
        lv.extend(([ValueItem("", Text("(no app)", "dim"))] if panel else [])
                  + [ValueItem(p, Text(p)) for p in drawing])
        self.mark_active()

    @on(Input.Changed, "#filter")
    def filter_changed(self, event: Input.Changed) -> None:
        """The count at once, the rows a beat later.

        Rebuilding the list costs a mount per row, and doing that on every
        keystroke made the field itself lag behind the typing. The count is
        cheap, so that part stays immediate.
        """
        self.show_packages(event.value, rows=False)
        if self._filtering is not None:
            self._filtering.stop()
        self._filtering = self.set_timer(0.15, lambda: self.show_packages(event.value))

    @on(ListView.Selected, "#devices")
    def device_selected(self, event: ListView.Selected) -> None:
        if isinstance(item := event.item, ValueItem):
            self.open_or_close(item.value)

    @work(group="panel")
    async def open_or_close(self, serial: str) -> None:
        await self.toggle_panel(serial)

    @on(ListView.Selected, "#packages")
    def package_selected(self, event: ListView.Selected) -> None:
        if isinstance(item := event.item, ValueItem):
            self.choose_package(item.value)

    @work(group="package")
    async def choose_package(self, package: str) -> None:
        if not (panel := self.target()):
            return
        panel.package = package or None
        panel.write(f"app [b]{panel.package}[/]" if package else "[dim]no app selected")
        self.sync_sidebar()
        await panel.package_chosen()
        await panel.refresh_stats()

    # ------------------------------------------------------ the active device

    @work(group="action")
    async def action_frida_server(self) -> None:
        """Toggle frida-server on the device."""
        if panel := self.target():
            await panel.toggle_frida()

    @work(group="action")
    async def action_frida_purge(self) -> None:
        """Take frida-server off the device entirely, binary and socket."""
        if panel := self.target():
            await panel.purge_frida()

    @work(group="action")
    async def action_frida_client(self) -> None:
        """Run frida against the selected app: spawned, or attached where it runs.

        The two guards below are spelled out here, in objection and in saving
        an app rather than shared: folding them into one helper cost the type
        narrowing that says panel.package is a string by the time it reaches
        an argument list, and a helper that has to be re-asserted at every
        call site is longer than the lines it saved.

        -f spawns and holds the app until the script is in, which is what a
        root or pinning bypass needs and the only thing this used to do. An app
        that is already up cannot be given that, and spawning it again throws
        away whatever state it is in — the session that was logged in, the
        screen that was reached. So where there is a pid, which of the two it
        is gets asked; enter and escape keep the spawn, which is what this
        always did.

        Attaching is also the only way to instrument an app nobody wants
        restarted, and the way to read what the device log does not carry: the
        unified log's debug and info entries never reach idevicesyslog, and a
        script on the running process sees them where they are made.
        """
        if not (panel := self.target()):
            return
        if not panel.package:
            panel.fail(NO_APP)
            return
        # -f, unless the app is up and attaching to it is what was wanted.
        target, label = ["-f", panel.package], ""
        # `is not None` rather than truthiness: it says what is meant — there
        # is a pid or there is not — and it is what narrows pid to a string
        # for the argument list below.
        pid = await panel.app_pid()
        if pid is not None and await self.push_screen_wait(ConfirmScreen(
                f"frida on {panel.package}",
                f"attach to it as it runs, pid {pid}",
                "spawn it again, for a script that has to be in before it starts")):
            # The label, because the command line now says a number: the pane's
            # border is where "which app is this" gets answered.
            target, label = ["-p", pid], f"frida {panel.package} (pid {pid})"
        prompt = FridaArgsScreen(
            f"frida arguments for {panel.package}", panel.frida_args,
            "--codeshare user/script  -l script.js  -l /path/other.js",
            panel.script_dir,
        )
        answer = await self.push_screen_wait(prompt)
        panel.script_dir = prompt.local_dir
        if answer is None:
            return
        panel.frida_args = answer
        try:
            extra = shlex.split(answer)
        except ValueError as exc:            # unbalanced quotes in the arguments
            panel.fail(f"bad frida arguments: {exc}")
            return
        if not await panel.ensure_frida():
            return
        if target[0] == "-p":            # attaching, so the app has to be awake
            await panel.wake_app()
        panel.start_tool(["frida", "-D", panel.serial, *target, *extra], label)

    @work(group="action")
    async def action_objection(self) -> None:
        """objection attaches to a *running* process through frida-server.

        `-n` and `start`, not `-g` and `explore`: upstream hid the gadget
        option and the explore command, both of which now print a deprecation
        notice and will go.

        Given a pid rather than the bundle id, which is the difference between
        this working on an iPhone and not. objection resolves `-n` in three
        steps — an integer pid, then a process name, then frida's application
        list — and on iOS only the first is dependable: a process there is
        named after the executable inside the bundle and not after the bundle
        id, and the application list carries a pid only for an app frida is
        already holding, which is why this used to work only after the frida
        client had spawned the app once and exited 1 otherwise. The pid is
        already in hand from the process table, so it is what goes.

        frida-server and a running app both have to be there first: without
        either, objection exits with "unable to find the target application"
        and says nothing about which of the two was missing. And on iOS
        running is not enough — see IosPanel.wake_app.
        """
        if not (panel := self.target()):
            return
        if not panel.package:
            panel.fail(NO_APP)
            return
        if not await panel.ensure_frida():
            panel.fail("objection needs frida-server on the device")
            return
        if pid := await panel.app_pid():
            # Running already, which on iOS is not the same as running now.
            await panel.wake_app()
        else:
            panel.write(f"starting {panel.package}…")
            if not await panel.launch_app():
                # Nothing here can start it: no launcher activity on android,
                # no open(1) on the phone. Said now rather than after ten
                # seconds of watching a process table that will not change.
                panel.fail(f"{panel.package} cannot be started from here —"
                           " open it on the device, then press o again")
                return
            # Ten seconds, not five: a cold start on an older phone takes
            # longer than that, and waiting costs nothing next to giving up on
            # an app that was on its way.
            for _ in range(20):
                await asyncio.sleep(0.5)
                if pid := await panel.app_pid():
                    break
            else:
                # What is left once the launch itself was accepted: a locked
                # screen, or an app that goes straight back down again.
                panel.fail(f"{panel.package} would not start — unlock the device,"
                           " start it there, then press o again")
                return
        # The label, because the command line now says a number: the pane's
        # border is where "which app is this" gets answered.
        panel.start_tool(["objection", "-S", panel.serial, "-n", pid, "start"],
                         f"objection {panel.package} (pid {pid})")

    def action_mirror(self) -> None:
        """Toggle the external window that mirrors this device's screen."""
        if not (panel := self.target()):
            return
        if panel.mirror and panel.mirror.poll() is None:
            reap(panel.mirror)
            panel.mirror = None
            panel.write(f"[dim]{panel.mirror_tool} closed")
            return
        if not shutil.which(panel.mirror_tool):
            panel.fail(f"{panel.mirror_tool} is not installed")
            return
        i = self.panels.index(panel)
        try:
            panel.mirror = subprocess.Popen(
                panel.mirror_argv(i), stdin=subprocess.DEVNULL,
                stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL, start_new_session=True,
            )
        except OSError as exc:      # on PATH but not runnable: a bad shebang, no fork
            panel.fail(f"{panel.mirror_tool}: {exc.strerror or exc}")
            return
        panel.write(f"{panel.mirror_tool} window {i + 1} (pid {panel.mirror.pid})")

    @work(group="action")
    async def action_shell(self) -> None:
        """A shell on the device, in the panel's pty — adb, or ssh.

        A worker rather than a plain handler: the iOS side has to have its
        tunnel up before ssh is spawned, and that is a call to iproxy.
        """
        if not (panel := self.target()):
            return
        argv, label = await panel.shell_argv()
        panel.start_tool(argv, label)

    @work(group="action")
    async def action_log(self) -> None:
        """Toggle this device's log stream: logcat, or the iOS syslog."""
        if not (panel := self.target()):
            return
        if panel.stop_stream(panel.log_stream):
            await panel.refresh_stats()
            return
        # A pid is the whole filter, on both families, so an app that is not
        # running has none — and being asked "only this app?" there offered a
        # narrowing that could not be applied and quietly gave back the whole
        # device anyway. Asked only where there is something to answer with.
        pid = await panel.app_pid() if panel.package else None
        if pid:
            # Whole device or one app: both are wanted, and which one is not
            # something to guess — a filter is invisible once it scrolls.
            if await self.push_screen_wait(ConfirmScreen(
                    f"{panel.log_stream} on {panel.serial}",
                    f"only {panel.package}, pid {pid}",
                    "everything on the device")):
                # A pid is the precise way to name a process and the
                # perishable one: the app restarting gets a new one, the
                # filter then matches nothing at all, and a log gone quiet for
                # that reason is worth knowing in advance of it happening.
                panel.write(f"[dim]filtering on pid [b]{pid}[/] — an app that restarts"
                            " gets a new one, so l twice to follow it[/]")
            else:
                pid = None
        elif panel.package:
            # Not installed is the one thing the app list knows for certain.
            # No pid is every other case at once — the app is down, or the
            # phone could not be asked because ssh is not up — and picking one
            # of those to print would be a guess wearing a fact's clothes.
            why = (f"{panel.package} is not installed on this device"
                   if panel.package not in panel.packages else f"no pid for {panel.package}")
            panel.write(f"[dim]{escape(why)}: the {panel.log_stream} is the whole device[/]")
        # log_keep is what the tool could not be asked for: see log_command.
        argv = await panel.log_command(pid or "")
        panel.start_stream(panel.log_stream, *argv, keep=panel.log_keep)

    def action_files(self) -> None:
        """Browse the device and push or pull files."""
        if panel := self.target():
            self.push_screen(FilesScreen(panel))

    @work(group="action")
    async def action_install(self) -> None:
        """Install an apk or an ipa picked off the host, in the browser `-l` uses."""
        if not (panel := self.target()):
            return
        picker = ScriptScreen(panel.local_dir, panel.installs)
        path = await self.push_screen_wait(picker)
        panel.local_dir = picker.side.path       # the browser reopens where it was
        if not path:
            return
        if not await self.push_screen_wait(ConfirmScreen(
                f"install {path}", f"install it on {panel.serial}", "cancel")):
            return
        rc, out = await panel.install(path)
        if rc != 0:
            panel.fail(out)
            return
        panel.write(escape(out))
        # It is installable and now installed: the sidebar has to list it.
        await panel.load_packages()
        self.sync_sidebar()

    @work(group="action")
    async def action_save_app(self) -> None:
        """Save the selected app off the device: the apk files, or a repacked ipa."""
        if not (panel := self.target()):
            return
        if not panel.package:
            panel.fail(NO_APP)
            return
        picker = ScriptScreen(panel.local_dir, panel.installs, pick_dir=True)
        dest = await self.push_screen_wait(picker)
        panel.local_dir = picker.side.path
        if dest:
            existing = await panel.existing_exports(dest)
            names = ", ".join(l.name for l in existing)
            if existing and not await self.push_screen_wait(ConfirmScreen(
                f"overwrite {names} in {dest}?", "overwrite", "cancel",
            )):
                panel.write("[dim]export cancelled — existing file not overwritten")
                return
            await panel.save_app(dest)

    @work(group="action")
    async def action_info(self) -> None:
        if panel := self.target():
            await panel.system_info()

    @work(group="action")
    async def action_login(self) -> None:
        """Set the credentials this device is reached with, where it needs any."""
        if panel := self.target():
            await panel.set_login()

    def action_clean(self) -> None:
        """Empty the active panel's log."""
        if panel := self.target():
            panel.query_one(f"#log-{panel.uid}", RichLog).clear()

    # ----------------------------------------------------------- this interface

    def action_screenshot(self) -> None:  # type: ignore[override]
        """An SVG of the interface, after a beat so the key press has settled."""
        self.set_timer(0.1, self.deliver_screenshot)

    def action_theme(self) -> None:
        dark, light = KEEP_THEMES
        self.theme = light if self.theme == dark else dark

    def action_keys(self) -> None:
        """Textual's key and widget help panel, on and off."""
        if self.screen.query("HelpPanel"):
            self.action_hide_help_panel()
        else:
            self.action_show_help_panel()

    @work(group="quit")
    async def action_quit(self) -> None:  # type: ignore[override]
        """Ask first, and name what is running: a panel can be holding a frida
        session, a log stream and a mirroring window, and q is next to every
        other key.
        """
        busy = [what for what, on in (
            ("a tool", any(p.term.running for p in self.panels)),
            ("a log", any(p.streams for p in self.panels)),
            ("a mirror", any(p.mirror and p.mirror.poll() is None for p in self.panels)),
        ) if on]
        leaving = f"stop {' and '.join(busy)}, then exit" if busy else "exit"
        if not await self.push_screen_wait(ConfirmScreen("quit moabile", leaving, "stay")):
            return
        for p in self.panels:
            await p.shutdown()
        self.exit()


def main(argv: list[str]) -> int:
    """The command line, which is a door and not a dashboard.

    A program that swallows arguments it does not understand and then paints
    the screen leaves you wondering which of the two you got wrong, so an
    argument it has no use for is an error with the usage under it.
    """
    if {"-h", "--help"} & set(argv):
        print(USAGE)
    elif {"-V", "--version"} & set(argv):
        print(f"moabile {VERSION}")
    elif argv:
        print(f"moabile takes no arguments: {shlex.join(argv)}\n\n{USAGE}", file=sys.stderr)
        return 2
    else:
        MOABile().run()
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
