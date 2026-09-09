#!/usr/bin/env python3
"""Headless checks for moabile, driven by fake tools on PATH.

    python3 test_moabile.py

Covers what silently breaks against real hardware: the startup gate, device
discovery, per-panel isolation across two devices, the embedded pty terminal,
the file browser on both filesystems, and the preconditions frida needs.
"""

import ast
import asyncio
import contextlib
import io
import os
import random
import re
import shlex
import shutil
import socket
import sys
import tarfile
import tempfile
import time
import zipfile
from pathlib import Path
from typing import Any, cast
from unittest.mock import patch

from textual import events

TMP = Path(tempfile.mkdtemp())

# emulator-5554 is deliberately NOT rooted, so the no-root paths get exercised.
FAKE_ADB = f"""#!/usr/bin/env bash
serial=""
if [[ $1 == -s ]]; then serial=$2; shift 2; fi
echo "$*" >> "{TMP}/adb-log"
if [[ -f "{TMP}/hostile" && "$*" != devices ]]; then
  head -c 300 /dev/urandom; python3 -c "print('x'*200000)"; printf "no trailing newline"; exit 1
fi
# adb hands the whole line to the device's shell, which strips one round of
# quoting before anything runs — so a su'd script arrives here quoted and the
# patterns below match what the device would actually have seen.
flat="${{*//"'"/}}"
case "$flat" in
  "--version")                 echo "Android Debug Bridge version 1.0.41";;
  "devices")                   echo "List of devices attached"
                               [[ -f "{TMP}/gone" ]] && exit 0
                               [[ -f "{TMP}/locked" ]] && {{ echo -e "emulator-5554\\tunauthorized"; exit 0; }}
                               [[ -f "{TMP}/hostile" ]] && {{ echo -e "emulator-5554\\tdevice"; exit 0; }}
                               echo "List of devices attached"
                               echo -e "emulator-5554\\tdevice"
                               [[ -f "{TMP}/unplugged" ]] || echo -e "emulator-5556\\tdevice";;
  "shell getprop")             [[ -f "{TMP}/noprops" ]] && {{
                                 echo "error: device offline" >&2; exit 1; }}
                               echo "[ro.product.model]: [Pixel ${{serial: -1}} [/] [bold]]"
                               echo "[ro.product.device]: [emu64x]"
                               echo "[ro.build.version.release]: [13]"
                               echo "[ro.build.version.sdk]: [33]"
                               echo "[ro.product.cpu.abi]: [arm64-v8a]";;
  "shell su -c id")            [[ $serial == emulator-5556 ]] && echo "uid=0(root)" || echo "su: not found"
                               exit 0;;
  "shell su -c"*nohup*)        touch "{TMP}/frida-up";;
  "shell su -c kill"*)         rm -f "{TMP}/frida-up";;
  "shell pm list packages -3") [[ -f "{TMP}/nopkgs" ]] && exit 0
                               [[ -f "{TMP}/hostile-pkg" ]] && {{
                                 echo "package:../../../../tmp/escaped"
                                 echo "package:com.evil app"; echo "package:/etc/passwd"; }}
                               echo "package:com.target.app"; echo "package:com.other.app"
                               [[ -f "{TMP}/installed" ]] && echo "package:com.fresh.app"
                               exit 0;;
  "shell pm list packages")    # Without -3 the device answers with the system's
                               # own too, which is not what the sidebar asks for.
                               echo "package:com.android.settings"
                               echo "package:com.target.app"; exit 0;;
  "shell pm path"*)            echo "package:/data/app/~~ab==/com.target.app-1/base.apk"
                               echo "package:/data/app/~~ab==/com.target.app-1/split_config.arm64.apk";;
  "install -r"*)               [[ -f "{TMP}/resigned" ]] && {{
                                 echo "adb: failed to install: Failure [INSTALL_FAILED_UPDATE_INCOMPATIBLE: signatures do not match newer version]"
                                 exit 1; }}
                               [[ -f "{TMP}/badapk" ]] && {{ echo "Failure [INSTALL_FAILED_INVALID_APK]"; exit 0; }}
                               touch "{TMP}/installed"; echo "Success";;
  "shell wm size")             echo "Physical size: 1080x2400";;
  "shell ls -pA"*|"shell su -c ls -pA"*)
                               [[ "$*" == *nowhere* ]] && {{ echo "ls: nowhere: No such file"; exit 1; }}
                               [[ -f "{TMP}/hostile-ls" ]] && {{
                                 echo "../"; echo "../../etc/"; echo "a/b.txt"; echo "."; }}
                               echo "Download/"; echo "Android/"; echo "note.txt";;
  "shell [ -f"*|"shell su -c [ -f"*)
                               [[ -f "{TMP}/server-there" ]] && echo 41943040; exit 0;;
  "shell test -e "*|"shell su -c test -e "*|"shell su -c 'test -e "*)
                               [[ "$*" == *existing* || "$*" == *clash* ]] && exit 0 || exit 1;;
  *"rm "*|*" mv "*)             echo "$*" >> "{TMP}/edits";;
  "push "*)                    # adb push is not root: the internal data
                               # directory refuses it, the way pull does below.
                               dst=${{@: -1}}
                               [[ $dst == /data/data/* ]] && {{
                                 echo "adb: error: failed to copy: Permission denied"
                                 exit 1; }}
                               echo "1 file pushed";;
  "pull "*)                    dst=${{@: -1}}; src=${{@: -2:1}}
                               [[ $src == /data/data/* ]] && {{ echo "adb: error: failed to stat: Permission denied"; exit 1; }}
                               [[ -d $dst ]] && dst="$dst/$(basename "$src")"
                               echo "pulled-from-$src" > "$dst"; echo "1 file pulled";;
  "exec-out su -c cat"*)       echo "root-only-bytes";;
  "shell monkey"*)             echo "$*" >> "{TMP}/monkey"
                               [[ -f "{TMP}/nolauncher" ]] && {{
                                 echo "** No activities found to run, monkey aborted."
                                 exit 0; }}
                               touch "{TMP}/running-$serial";;
  "shell pidof com.target.app")
                               # Only the app that is actually installed and up:
                               # pidof answers nothing for anything else, which
                               # is how the panel tells the two apart.
                               [[ -f "{TMP}/running-$serial" ]] && echo 4242; exit 0;;
  "shell pidof"*)              exit 0;;
  "shell pgrep"*|"shell su -c pgrep"*)
                               [[ -f "{TMP}/frida-up" ]] && {{ echo 9001; exit 0; }} || exit 1;;
  *@model*)                    echo "@model";    echo "Google"; echo "Pixel"
                               echo "@timezone"; echo "Europe/Rome"
                               echo "@selinux";  echo "Enforcing"
                               echo "@kernel";  echo "5.10.0"
                               echo "@su";      echo "/system/xbin/su"
                               exit 0;;
  *@batt*)                     [[ -f "{TMP}/nostats" ]] && {{
                                 echo "error: closed" >&2; exit 1; }}
                               [[ -f "{TMP}/slow" ]] && sleep 3
                               echo "@batt";  echo "  level: 87"
                               echo "@load";  echo "0.42 0.31 0.28 1/900 1234"
                               echo "@mem";   echo "MemTotal:        4000000 kB"
                                              echo "MemAvailable:    1500000 kB"
                               echo "@ip"
                               [[ -f "{TMP}/noroute" ]] \
                                 || echo "192.168.1.0/24 dev wlan0 src 192.168.1.44"
                               echo "@frida"
                               # A device with no pgrep answers with a digit of
                               # its own, which is not a pid: see @frida below.
                               if [[ -f "{TMP}/nopgrep" ]]
                                 then echo "sh: 1: pgrep: not found"
                                 elif [[ -f "{TMP}/frida-up" ]]; then echo 9001
                               fi
                               [[ "$*" == *"@pid"* ]] && {{ echo "@pid"; echo "4242"; }}
                               # A shell exits with its last command's status,
                               # and this batch ends in pgrep, or in pidof where
                               # an app is selected: both exit 1 having matched
                               # nothing, which is not the device going away.
                               if [[ "$*" == *"@pid"* ]]
                                 then [[ -f "{TMP}/running-$serial" ]]; exit $?
                               fi
                               [[ -f "{TMP}/nopgrep" ]] && exit 127
                               [[ -f "{TMP}/frida-up" ]]; exit $?;;
  "logcat"*)                   echo "D/App( 42): running"; sleep 30;;
  *)                           exit 0;;
esac
"""

bindir = TMP / "bin"
bindir.mkdir()
IOS_UDID = "00008030001122334455667788AABBCC"


def fake(name: str, body: str) -> None:
    (bindir / name).write_text(f"#!/usr/bin/env bash\n{body}\n")
    (bindir / name).chmod(0o755)


(bindir / "adb").write_text(FAKE_ADB)
(bindir / "adb").chmod(0o755)
# A real frida wheel can print a warning first, and sh() folds stderr in.
fake("frida", 'echo "DeprecationWarning: whatever" >&2; echo "16.5.9"')
# objection has no --version: it is a click program, and the number is behind
# a subcommand. Asked for the option it answers the way click does.
fake("objection", '''case "$1" in
  version)      echo "objection: 1.11.0";;
  --version|-V) echo "Error: No such option: $1" >&2; exit 2;;
  *)            echo "objection: 1.11.0";;
esac''')
# A real frida-server is tens of megabytes; the app rejects anything smaller,
# so the fake has to produce a believable one. Touch TMP/tiny for the
# truncated-download case.
CURL = (
    f'echo "$*" >> "{TMP}/curl-log"\n'
    # codeshare pages: canned HTML, or a refused connection with TMP/netdown.
    f'case "$*" in\n'
    f'  *--version*) echo "curl 8.5.0 (x86_64-pc-linux-gnu) libcurl/8.5.0"; exit 0;;\n'
    f'  *codeshare*)\n'
    f'    [[ -f "{TMP}/netslow" ]] && sleep 2\n'
    f'    [[ -f "{TMP}/netdown" ]] && {{ echo "curl: (7) Failed to connect to codeshare.frida.re" >&2; exit 7; }}\n'
    f'    case "$*" in\n'
    f'      *search*) [[ -f "{TMP}/nohits" ]] && {{ cat "{TMP}/nohits.html"; exit 0; }}\n'
    f'                cat "{TMP}/search.html";;\n'
    f'      *)        cat "{TMP}/browse.html";;\n'
    f'    esac\n'
    f'    exit 0;;\n'
    f'esac\n'
    f'[[ -f "{TMP}/tiny" ]] && {{ printf "TRUNCATED"; exit 0; }}\n'
    # the ios build ships as a package, not a bare binary
    f'case "$*" in *.deb) cat "{TMP}/frida.deb"; exit 0;; esac\n'
    'printf "FAKE-FRIDA-SERVER-PAYLOAD"\n'
    'dd if=/dev/zero bs=1024 count=1200 2>/dev/null | tr "\\0" "F"'
)


def ar_member(name: str, blob: bytes) -> bytes:
    """One member of an ar archive: a fixed-width header, then the bytes."""
    head = f"{name:<16}{'0':<12}{'0':<6}{'0':<6}{'100644':<8}{len(blob):<10}"
    return head.encode() + b"`\n" + blob + (b"\n" if len(blob) % 2 else b"")


def make_deb(path: Path) -> None:
    """A real .deb: an ar archive whose data member is a tar of the two files.

    Random payload on purpose — the app rejects a download too small to be a
    build, and anything repetitive would compress under that floor.
    """
    inner = io.BytesIO()
    with tarfile.open(fileobj=inner, mode="w:gz") as tar:
        for name in ("./var/jb/usr/sbin/frida-server",
                     "./var/jb/usr/lib/frida/frida-agent.dylib"):
            blob = b"FAKE-FRIDA-PAYLOAD" + os.urandom(700_000)
            info = tarfile.TarInfo(name)
            info.size, info.mode = len(blob), 0o755
            tar.addfile(info, io.BytesIO(blob))
    data = inner.getvalue()
    path.write_bytes(b"!<arch>\n" + ar_member("debian-binary", b"2.0\n")
                     + ar_member("data.tar.gz", data))
    assert path.stat().st_size > 1_000_000, path.stat().st_size


make_deb(TMP / "frida.deb")


# codeshare.frida.re markup, copied from the real pages: the parser reads the
# slug out of the URL, the likes out of the icon line, and the pager out of the
# ?page= links, so a fake missing any of those would prove nothing.
def article(owner: str, slug: str, title: str, likes: str, about: str) -> str:
    return f"""
        <article>
          <h2><a href="https://codeshare.frida.re/@{owner}/{slug}/">{title}</a></h2>
          <h3>
            <i class="fa fa-thumbs-o-up" aria-hidden="true"></i> {likes} | <i class="fa fa-eye" aria-hidden="true"></i> 27K
          </h3>
          <h4>Uploaded by: <a href="/@{owner}/">@{owner}</a></h4>
          <p>{about}</p>
          <ul class="actions">
            <li><a href="https://codeshare.frida.re/@{owner}/{slug}/" class="button">Project Page</a></li>
          </ul>
        </article>"""


PAGER = "".join(f'<li><a href="?page={n}">{n}</a></li>' for n in (2, 3, 4))
(TMP / "browse.html").write_text(
    "<div>"
    + article("oleavr", "ios-jailbreak-detection-bypass",
              "ios-jailbreak-detection-bypass", "31", "Bypass jailbreak checks")
    + article("ub3rsick", "rootbeer-root-detection-bypass",
              "RootBeer root detection bypass", "12", "rootbeer library bypass")
    + article("dzonerzy", "fridantiroot", "fridantiroot", "54", "Android antiroot checks bypass")
    + f'</div><ul class="pagination">{PAGER}</ul>'
)
# What codeshare actually answers with when nothing matches: an <article> that
# holds a message and no project link at all.
(TMP / "nohits.html").write_text(
    '<div><article><h3>No results found for "zzqqxx7"</h3>'
    '<p>Try a different search term or <a href="/browse">browse all projects</a>.</p>'
    "</article></div>"
)
# 15 hits, so they do not fit one page of the browser and have to be cut.
(TMP / "search.html").write_text(
    "<div>" + "".join(article("rootbeer", f"hit-{n}", f"hit {n}", str(n), f"rootbeer hit {n}")
                      for n in range(1, 16)) + "</div>"
)
# ---------------------------------------------------------------- the iPhone
# usbmux for what needs no cooperation from the phone, ssh for the rest. The
# ssh fake answers the scripts moabile actually sends, so the whole iOS side is
# exercised without a device: the last argument is the remote command.
FAKE_SSH = f"""#!/usr/bin/env bash
# The socket -M would create and the rest ride: "$*" as one string, since
# ${{*#pattern}} strips the pattern from every argument separately.
args="$*"; sock=""
[[ $args == *ControlPath=* ]] && {{ sock="${{args#*ControlPath=}}"; sock="${{sock%% *}}"; }}
case "$*" in
  --version)    echo "unknown option -- -" >&2
                echo "usage: ssh [-46AaCfGgKkMNnqsTtVvXxYy] [-B bind_interface]" >&2
                exit 255;;
  -V)           echo "OpenSSH_9.6p1, OpenSSL 3.0.11"; exit 0;;
  *"-O check")  [[ -f "{TMP}/ssh-master" ]] \
                  && kill -0 "$(cat "{TMP}/ssh-master")" 2>/dev/null && exit 0
                exit 1;;
  *"-O exit")   rm -f "{TMP}/ssh-master" ${{sock:+"$sock"}}; exit 0;;
  *"-M -N")     # The real one refuses a socket that is already there and drops
                # to an unmultiplexed connection nothing else can ride.
                [[ -e "$sock" ]] && {{
                  echo "ControlSocket $sock already exists, disabling multiplexing"
                  exit 1
                }}
                want=alpine
                [[ -f "{TMP}/ios-pw-changed" ]] && want=not-alpine
                silent=-s; [[ -f "{TMP}/ios-echo-on" ]] && silent=-r
                printf "(mobile@localhost) Password for mobile@fake-iPhone: "
                read -r $silent pw
                if [[ $pw == $want ]]; then
                  echo $$ > "{TMP}/ssh-master"
                  # And it leaves that socket behind when it is killed rather
                  # than asked to close, which is what has to be cleared.
                  : > "$sock"; exec tail -f "{TMP}/ssh-master"
                fi
                [[ -f "{TMP}/ios-quiet-refusal" ]] && exit 1
                echo; echo "Permission denied, please try again."
                printf "(mobile@localhost) Password for mobile@fake-iPhone: "
                read -r $silent pw; exit 1;;
esac
[[ -f "{TMP}/ssh-master" ]] || {{ echo "ssh: no master" >&2; exit 255; }}
script="${{@: -1}}"
echo "$*" >> "{TMP}/ssh-log"
# Every command the panel sends starts with the PATH export a non-interactive
# ssh does not give it. Stripped so the cases below match the command itself,
# and remembered: this phone is a rootless jailbreak, whose grep and open live
# under /var/jb and are not there at all without it.
onpath=0
case "$script" in "export PATH="*) onpath=1; script="${{script#*;}}";; esac
case "$script" in
  "sudo -S -p '' sh -c "*)
                      read -r pw
                      [[ -f "{TMP}/ios-nosudo" || $pw != alpine ]] \
                        && {{ echo "sudo: incorrect password" >&2; exit 1; }}
                      eval "set -- ${{script#*sh -c }}"; script=$1
                      # sudo hands its own secure_path to the shell it starts,
                      # so the export is inside the quoting as well as outside.
                      case "$script" in
                        "export PATH="*) script="${{script#*;}}";;
                        *) onpath=0;;
                      esac;;
esac
case "$script" in
  *@load*)              poll=$(( $(cat "{TMP}/ios-poll" 2>/dev/null || echo 0) + 1 ))
                        echo $poll > "{TMP}/ios-poll"
                        # On the even polls the address errors arrive while the
                        # load section is still open: ssh folds the far end's
                        # stderr in wherever it lands, not where it belongs.
                        [[ -f "{TMP}/ios-noipcmd" ]] && (( poll % 2 == 0 )) && {{
                          echo "sh: ifconfig: not found" >&2; }}
                        # A phone whose sysctl is not on the ssh PATH — every
                        # rootless jailbreak, until the poll started saying so.
                        [[ -f "{TMP}/ios-nopath" ]] && {{
                          echo "sh: sysctl: not found" >&2; exit 127; }}
                        echo "@load";  echo "{{ 0.55 0.40 0.31 }}"
                        echo "@mem";   echo "4294967296"
                        echo "Mach Virtual Memory Statistics: (page size of 16384 bytes)"
                        echo "Pages free:                          65536."
                        echo "Pages inactive:                       1024."
                        echo "@ip"
                        # Only if the batch asked: once the panel has been told
                        # the phone has none of the four it stops sending them,
                        # and a fake that answers anyway hides that.
                        if [[ "$script" != *ipconfig* ]]
                          then :
                        # No ipconfig and no wifi: an empty section, which is
                        # an answer — the phone has no address.
                          elif [[ -f "{TMP}/ios-noipcmd" ]]
                          then # None of them on the phone, and on the odd polls
                               # that is what this section says. On the even ones
                               # it says nothing and the errors came out above.
                               if (( poll % 2 == 1 )); then
                                 echo "sh: ipconfig: not found" >&2
                                 echo "sh: ifconfig: not found" >&2
                                 echo "sh: scutil: not found" >&2
                               fi
                          elif [[ -f "{TMP}/ios-scutil" ]]
                          then echo "   address : 10.1.2.3"
                          elif [[ -f "{TMP}/ios-ifconfig" ]]
                          then # What ifconfig -a prints when ipconfig is not
                               # there: tabs, the loopback first, inet6 beside
                               # the address that is wanted.
                               printf '\tinet 127.0.0.1 netmask 0xff000000\n'
                               printf '\tinet6 fe80::1 prefixlen 64\n'
                               printf '\tinet 10.0.0.5 netmask 0xffffff00 broadcast 10.0.0.255\n'
                          elif [[ ! -f "{TMP}/ios-noip" ]]
                          then echo "192.168.1.77"
                        fi
                        echo "@ps"
                        echo "    1 /sbin/launchd"
                        [[ -f "{TMP}/ios-frida" ]] && echo " 9101 /usr/sbin/frida-server"
                        [[ -f "{TMP}/ios-running" ]] && echo " 4321 /var/containers/Bundle/Application/AA-BB/Target.app/Target"
                        exit 0;;
  *@kernel*)            echo "@kernel";     echo "Darwin iPhone 21.6.0 arm64"
                        echo "@uptime";     echo "12:00 up 3 days"
                        echo "@storage";    echo "/dev/disk0s1s1  59G  22G  37G  38% /"
                        echo "@net"
                        [[ -f "{TMP}/ios-noipcmd" ]] \
                          && echo "sh: ipconfig: not found" >&2 \
                          || echo "192.168.1.77"
                        echo "@jailbreak";  echo "/Applications/Sileo.app"
                        echo "@dpkg";       echo "/usr/bin/dpkg"
                        echo "@ps"
                        echo "    1 /sbin/launchd"
                        echo "  312 /usr/libexec/backboardd"
                        [[ -f "{TMP}/ios-frida" ]] && echo " 9101 /usr/sbin/frida-server"
                        exit 0;;
  id*)                  echo "uid=0(root) gid=0(wheel)"
                        [[ -f "{TMP}/rootless" ]] && echo "@rootless"; exit 0;;
  "tar cf - -C "*)      rest=${{script#tar cf - -C }}
                        parent=${{rest%% *}}; name=${{rest#* }}
                        [[ "$parent" == *nowhere* ]] && {{ echo "tar: nowhere" >&2; exit 1; }}
                        staging=$(mktemp -d)
                        case "$name" in
                          *.app) mkdir -p "$staging/$name"
                                 echo "fake-macho"    > "$staging/$name/Target"
                                 echo "plist"         > "$staging/$name/Info.plist";;
                          *)     echo "pulled-from-$parent/$name" > "$staging/$name";;
                        esac
                        tar cf - -C "$staging" "$name"
                        rm -rf "$staging"; exit 0;;
  "ls -pA"*)            [[ "$script" == *nowhere* ]] && {{ echo "ls: nowhere"; exit 1; }}
                        echo "Media/"; echo "Library/"; echo "note-ios.txt"; exit 0;;
  "test -e "*)          [[ "$script" == *existing* || "$script" == *clash* ]] && exit 0 || exit 1;;
  "rm -f"*|"rm -rf"*|"mv "*)
                        echo "$script" >> "{TMP}/ios-edits"; exit 0;;
  "["*frida-agent*)     [[ -f "{TMP}/ios-agent-there" ]] && exit 0; exit 1;;
  "["*frida-server*)    [[ -f "{TMP}/ios-server-there" ]] && echo 20971520; exit 0;;
  *"frida-server --version")
                        cat "{TMP}/ios-frida-version" 2>/dev/null || echo "16.5.9"; exit 0;;
  chmod*)               exit 0;;
  *nohup*frida-server*) touch "{TMP}/ios-frida"; exit 0;;
  "kill -9"*)           rm -f "{TMP}/ios-frida"; exit 0;;
  *"ps -A -o pid,comm"*)
                        [[ -f "{TMP}/ios-noprocps" ]] && {{
                          echo "sh: 1: ps: not found" >&2; exit 127; }}
                        echo "    1 /sbin/launchd"
                        [[ -f "{TMP}/ios-frida" ]] && echo " 9101 /usr/sbin/frida-server"
                        [[ -f "{TMP}/ios-running" ]] \
                          && echo " 4321 /var/containers/Bundle/Application/AA-BB/Target.app/Target"
                        # The helper an app ships beside it: a pid for a name
                        # matched anywhere in the line, and the wrong one.
                        echo " 4322 /var/containers/Bundle/Application/AA-BB/Target.app/TargetHelper"
                        exit 0;;
  "grep -ls"*metadata.plist*)
                        (( onpath )) || {{ echo "sh: grep: not found" >&2; exit 127; }}
                        echo "/var/mobile/Containers/Data/Application/CC-DD/.com.apple.mobile_container_manager.metadata.plist"
                        exit 0;;
  "grep -ls"*)          (( onpath )) || {{ echo "sh: grep: not found" >&2; exit 127; }}
                        # A phone with no grep at all, saying nothing: the
                        # 2>/dev/null the panel sends takes the shell's own
                        # "not found" with the glob noise it is there for, so
                        # the status is all that is left of it.
                        [[ -f "{TMP}/ios-nogrep" ]] && exit 127
                        [[ -f "{TMP}/ios-nobundle" ]] && exit 1
                        echo "/var/containers/Bundle/Application/AA-BB/Target.app/Info.plist"
                        exit 0;;
  open*)                (( onpath )) || {{ echo "sh: open: not found" >&2; exit 127; }}
                        [[ -f "{TMP}/ios-noopen" ]] && {{
                          echo "sh: open: command not found" >&2; exit 127; }}
                        # Refused with nothing to say, which is the half that
                        # used to be swallowed for having no output.
                        [[ -f "{TMP}/ios-open-mute" ]] && exit 3
                        # No open, and no words for it either: some shells put
                        # that message somewhere this end never sees, and 127
                        # is all that is left of it.
                        [[ -f "{TMP}/ios-open-gone" ]] && exit 127
                        # A phone that keeps open where mobile cannot reach it.
                        [[ -f "{TMP}/ios-open-needs-root" && "$args" != *sudo* ]] && {{
                          echo "open: Operation not permitted" >&2; exit 1; }}
                        echo "$script" >> "{TMP}/ios-open"; touch "{TMP}/ios-running"; exit 0;;
  *)                    exit 0;;
esac
"""
# scp of an .app is a directory copy: the repack has to find a bundle there.
FAKE_SCP = f"""#!/usr/bin/env bash
echo "$*" >> "{TMP}/scp-log"
dst="${{@: -1}}"; src="${{@: -2:1}}"
case "$dst" in
  *@*:/var/mobile/*) echo "$*" >> "{TMP}/scp-staged"; exit 0;;
  mobile@*:*)        echo "scp: $dst: Permission denied" >&2; exit 1;;
  *@*:*)             exit 0;;           # host -> phone as root: nothing to fake
esac
src="${{src#*:}}"
case "$src" in
  *.app) app="$dst/$(basename "$src")"; mkdir -p "$app"
         echo "fake-macho" > "$app/Target"; echo "plist" > "$app/Info.plist";;
  *)     name="${{src##*/}}"; [[ -d $dst ]] && dst="$dst/$name"
         echo "pulled-from-$src" > "$dst";;
esac
echo "1 file copied"
"""
(bindir / "ssh").write_text(FAKE_SSH)
(bindir / "ssh").chmod(0o755)
(bindir / "scp").write_text(FAKE_SCP)
(bindir / "scp").chmod(0o755)
fake("iproxy", f'''case "$*" in
  --version) echo "iproxy 2.0.2"; exit 0;;
  --help)    echo "Usage: iproxy [OPTIONS] LOCAL_PORT:DEVICE_PORT"
             echo "  -u, --udid UDID"; exit 0;;
esac
echo "$*" >> "{TMP}/iproxy-log"
[[ -f "{TMP}/iproxy-dies" ]] && exit 1
# Binds the port the way the real one does: that bind is the signal the app
# waits on to call the tunnel up, and a fake that only sleeps let it wait out
# the whole deadline every time. exec, so terminating the tunnel reaches the
# listener rather than leaving it orphaned behind the shell. Real ports, so
# two copies of this suite cannot run at once — the second one finds 2222
# taken and the test that pins it to IOS_SSH_PORT fails.
port="${{1%%:*}}"
exec python3 -c "
import os, socket, sys, time
s = socket.socket()
s.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEADDR, 1)
# A second of trying, because the run before this one may still be letting the
# port go: its listener is killed with the app and the kernel takes a moment
# over it. Inside the three seconds the app waits for the bind, so a port that
# is genuinely somebody else's still comes back as an iproxy that exited.
for attempt in range(10):
    try:
        s.bind(('127.0.0.1', int(sys.argv[1])))
        break
    except OSError:
        time.sleep(0.1)
else:
    sys.exit(1)
s.listen(8)
# Goes when whatever started it goes. A suite that aborts part way through
# would otherwise leave this holding the port, and the next run would find
# 2222 taken and fail somewhere that says nothing about why.
parent = os.getppid()
while os.getppid() == parent:
    time.sleep(0.05)
" "$port"''')
fake("idevice_id", f'''case "$*" in
  --version) echo "idevice_id 1.3.0"; exit 0;;
  -l)        [[ -f "{TMP}/ios" ]] && echo "{IOS_UDID}"; exit 0;;
esac''')
fake("ideviceinfo", f'''case "$*" in
  --version)                 echo "ideviceinfo 1.3.0"; exit 0;;
  *BatteryCurrentCapacity*)  echo batt >> "{TMP}/battery-log"; echo 77; exit 0;;
esac
[[ -f "{TMP}/ios-untrusted" ]] && {{ echo "ERROR: Could not connect: pairing" >&2; exit 1; }}
echo "DeviceName: Test iPhone [/] [bold]"
echo "ProductType: iPhone14,2"
echo "ProductVersion: 16.7.2"
echo "BuildVersion: 20H115"
echo "CPUArchitecture: arm64e"
echo "SerialNumber: F2LX0000001"
echo "WiFiAddress: 0a:bb:0c:dd:ee:ff"''')
fake("ideviceinstaller", f'''case "$*" in
  --version) echo "ideviceinstaller 1.1.1"; exit 0;;
  --help)    echo "Usage: ideviceinstaller COMMAND [OPTIONS]"
             echo "  list          list apps"
             echo "  install PATH  install an ipa"; exit 0;;
esac
echo "$*" >> "{TMP}/installer-log"
case "$*" in
  *list*|*" -l"*)
             [[ -f "{TMP}/ios-noapps" ]] && exit 0
             # With --attribute the columns are the ones asked for, and the
             # first line printed is their names. Without it, three fixed ones.
             if [[ "$*" == *CFBundleExecutable* ]]
               then echo "CFBundleIdentifier, CFBundleDisplayName, CFBundleExecutable, Path"
                    echo "com.target.ios, \\"My Target App\\", \\"Target\\", \\"/var/containers/Bundle/Application/AA-BB/Target.app\\""
               else echo "CFBundleIdentifier, CFBundleVersion, CFBundleDisplayName"
                    echo "com.target.ios, \\"1.0\\", \\"My Target App\\""
             fi
             # Only with every type asked for, exactly like the real one: plain
             # `list` is the user's own apps and nothing else.
             [[ "$*" == *--all* || "$*" == *list_all* ]] && {{
               echo "com.apple.mobilesafari, \\"Safari\\", \\"MobileSafari\\", \\"/Applications/MobileSafari.app\\""
               echo "com.apple.Maps, \\"Maps\\", \\"Maps\\", \\"/Applications/Maps.app\\""
               [[ -f "{TMP}/ios-trollstore" ]] && echo "com.opa334.TrollStore, \\"TrollStore\\", \\"TrollStore\\", \\"/var/containers/Bundle/Application/TS-TS/TrollStore.app\\""; }}
             exit 0;;
  *install*) [[ -f "{TMP}/badipa" ]] && {{ echo "ERROR: APIInternalError"; exit 0; }}
             [[ -f "{TMP}/unsigned" ]] && {{
               echo "ERROR: could not locate iTunesMetadata.plist in archive"
               echo "ERROR: ApplicationVerificationFailed"; exit 1; }}
             echo "Install: Complete"; exit 0;;
esac''')
fake("idevicesyslog", f'''case "$*" in
  --version) echo "idevicesyslog 1.3.0"; exit 0;;
  --help)    echo "Usage: idevicesyslog [OPTIONS]"; echo "  -p, --process PROCESS"; exit 0;;
esac
echo "$*" >> "{TMP}/syslog-log"
# The pid the process table reports for the app, and a line from another
# process: -p is a name filter, so both arrive whatever it was given.
if [[ -f "{TMP}/ios-syslog-noise" ]]
  then for i in $(seq 1 400); do
         echo "Aug 27 12:00:02 iPhone otherd(Foo)[62] <Notice>: noise $i"
       done
  else echo "Aug 27 12:00:00 iPhone Target(UIKit)[4321] <Notice>: running"
       echo "Aug 27 12:00:01 iPhone SpringBoard(FrontBoard)[62] <Notice>: not the app"
fi
sleep 30''')
# frida-ps is asked for nothing now that the app list has one source, but the
# gate still checks frida-tools and the fake has to answer --version.
fake("frida-ps", f'''[[ "$*" == "--version" ]] && {{ echo "16.5.9"; exit 0; }}
echo "$*" >> "{TMP}/frida-ps-log"
[[ -f "{TMP}/ios-frida" ]] || {{ echo "Failed to enumerate applications" >&2; exit 1; }}
echo "  PID  Name          Identifier"
echo "-----  ------------  ----------------------"
[[ -f "{TMP}/ios-running" ]] && echo " 4600  My Target App  com.target.ios"
echo " 4311  Safari         com.apple.mobilesafari"
[[ "$*" == *-ai* ]] && {{
  [[ -f "{TMP}/ios-running" ]] || echo "    -  My Target App  com.target.ios"
  echo "    -  Maps           com.apple.Maps"
}}
exit 0''')
fake("ip", f'''[[ "$*" == "neigh show" ]] || exit 1
echo "$*" >> "{TMP}/arp-log"
[[ -f "{TMP}/no-arp" ]] && exit 0
# macOS arp drops the leading zero of an octet; lockdownd never does.
echo "10.9.9.9 dev wlan0 lladdr a:bb:c:dd:ee:ff REACHABLE"
exit 0''')
fake("curl", CURL)
# The gate asks for a version; the download pipes a body through it.
fake("xz", '[[ "$*" == "--version" ]] && { echo "xz 5.4"; exit 0; }\ncat')
os.environ["PATH"] = f"{bindir}:{os.environ['PATH']}"
os.environ["HOME"] = str(TMP)          # must precede the import: CACHE is module-level
# What the directory this was started from held, and then out of it. A panel
# opens the file picker on the working directory, so e and s together — save
# the app, here — write an apk wherever the suite happens to be standing, and
# that used to be the checkout. Run from the temporary directory instead, and
# check the other one at the end.
STARTED_IN = Path.cwd()
WAS_THERE = {p.name for p in STARTED_IN.iterdir()}
os.chdir(TMP)

from rich.console import Console
from textual.app import App
from textual.color import Color
from textual.content import Content
from textual.markup import MarkupError
from textual.widgets import Input, Label, ListView, RichLog, Static
from textual.widgets._footer import FooterKey

import moabile


async def on_screen(pilot, app, cls, tries=80) -> bool:
    """Wait for a screen of this type to be up *and* composed.

    settle() alone returns on the frame the screen is pushed, which is one
    frame before its own compose() has run — so every test reaching for a
    widget by id on the next line was racing the mount. pilot.pause() waits
    for exactly that. This is what made the password screen fail one run in
    three with "No nodes match '#answer'".
    """
    if not await settle(pilot, lambda: isinstance(app.screen, cls), tries):
        return False
    await pilot.pause()
    return True


async def settle(pilot, predicate, tries=80):
    for _ in range(tries):
        await pilot.pause(0.05)
        if predicate():
            return True
    return False


def select(lv: ListView, value: str) -> None:
    lv.index = [getattr(n, "value", None) for n in lv._nodes].index(value)
    lv.action_select_cursor()


async def confirm(pilot, app, answer: str = "y") -> None:
    """Answer the yes/no screen that every destructive step puts up."""
    assert await on_screen(pilot, app, moabile.ConfirmScreen), app.screen
    await pilot.press(answer)


def _stats(panel) -> str:
    return str(panel.query_one(f"#stats-{panel.uid}").render())


def log_text(panel) -> str:
    """Everything the panel's log holds, as one string with the wrap taken out.

    RichLog stores rows already wrapped to the panel's width, so a message
    wider than that arrives split — and every assert on a phrase longer than
    a few words was passing only because of where the wrap happened to fall.
    The padding a row was written with stays: the log's columns are something
    these checks read too. Only the wrap's own trailing space goes, and the
    rows join with one space, so a message reads as the one thing it was.
    """
    rows = [strip.text.rstrip() for strip in panel.query_one(RichLog).lines]
    return " ".join(rows)


def term_text(panel) -> str:
    return str(panel.term.render())


def test_controlling_terminal() -> None:
    """A program on a pty gets it as its controlling terminal, not just stdin.

    ssh reads a password from /dev/tty and from nowhere else, and /dev/tty
    exists only for a process that has claimed one. setsid alone does not:
    without the ioctl the ssh master never saw a prompt to answer and sat
    there until it timed out, while the shell in the terminal pane worked
    fine — a shell reopens the terminal itself and papers over the missing
    claim, which is why only ssh noticed.
    """
    probe = ("import os,sys\n"
             "try:\n"
             "    os.close(os.open('/dev/tty', os.O_RDWR)); sys.stdout.write('HAVE')\n"
             "except OSError:\n"
             "    sys.stdout.write('NONE')\n")
    proc, fd = moabile.spawn_on_pty([sys.executable, "-c", probe])
    proc.wait(timeout=10)
    time.sleep(0.2)
    os.set_blocking(fd, False)
    try:
        said = os.read(fd, 4096).decode(errors="replace")
    except OSError:
        said = ""
    os.close(fd)
    assert "HAVE" in said, f"the child was given no controlling terminal: {said!r}"
    print("PASS a program spawned on a pty gets it as its controlling terminal")


async def test_logo_only_where_it_fits() -> None:
    """Shown on a terminal with room for it, skipped on one without.

    Half of a logo is worse than none, and it sits in front of the screen that
    says which tools are missing — so on a small terminal it does not appear.
    """
    big = moabile.MOABile()
    async with big.run_test(size=(moabile.LOGO_COLS + 8, moabile.LOGO_ROWS + 8)) as pilot:
        assert await settle(pilot, lambda: isinstance(big.screen, moabile.LogoScreen)), big.screen
        # It leaves on its own: a keypress to get past a logo, on every launch,
        # is a toll. Pressing one only hurries it.
        assert await settle(pilot, lambda: isinstance(big.screen, moabile.DepsScreen),
                            tries=200), big.screen
        await pilot.press("q")

    small = moabile.MOABile()
    async with small.run_test(size=(20, 6)) as pilot:
        assert await settle(pilot, lambda: isinstance(small.screen, moabile.DepsScreen)), \
            small.screen
        assert not any(isinstance(screen, moabile.LogoScreen)
                       for screen in small.screen_stack), "a logo with its head cut off"
        await pilot.press("q")
    print("PASS the logo is shown where it fits and skipped where it does not")


async def test_hostile_device() -> None:
    """Everything the device says is garbage: binary, enormous, truncated, failing."""
    (TMP / "hostile").touch()
    try:
        app = moabile.MOABile()
        async with app.run_test() as pilot:
            assert await on_screen(pilot, app, moabile.DepsScreen)
            await pilot.press("enter")
            assert await settle(pilot, lambda: bool(app.panels), tries=200), "no panel opened"
            panel = app.panels[0]
            for _ in range(3):
                await panel.refresh_stats()
            await pilot.press("t")           # a shell on a device answering garbage
            await pilot.pause(0.3)
            panel.term.stop()
            await pilot.press("l")
            await pilot.pause(0.2)
            await pilot.press("l")
            await pilot.press("f")
            await pilot.pause(0.4)
            assert app.panels, "the panel died on garbage output"
            assert "pid" not in log_text(panel).split("still running")[-1][:4], \
                log_text(panel)[-80:]
    finally:
        (TMP / "hostile").unlink()
    print("PASS a device answering only garbage does not take the app down")


async def test_vanishing() -> None:
    """A device unplugged while something of its own is still in flight.

    A modal answered after the panel is gone, a tool spawn that lands a frame
    late, a tool stopped inside that same frame, and a fetch that outlives the
    screen that started it. All of them are one shape: something resumes and
    reaches for a widget that is no longer there. run_test re-raises whatever a
    worker threw, so reaching the end of this is the result.
    """
    (TMP / "frida-up").touch()               # so s finds a server and gets that far
    app = moabile.MOABile()
    try:
        async with app.run_test() as pilot:
            assert await on_screen(pilot, app, moabile.DepsScreen)
            await pilot.press("enter")
            assert await settle(pilot, lambda: bool(app.panels), tries=200), "no panel"
            await app.toggle_panel("emulator-5556")          # the rooted one
            panel = app.panel("emulator-5556")
            assert panel is not None, app.panels
            panel.package = "com.target.app"
            panel.focus()
            await pilot.pause()

            # s asks for the frida arguments, and the cable comes out while the
            # question is up: the answer arrives for a panel with no pane left
            # to run anything in.
            await pilot.press("s")
            assert await on_screen(pilot, app, moabile.FridaArgsScreen), app.screen
            pane = panel.term
            await panel.shutdown()
            await panel.remove()
            await pilot.press("enter")
            await pilot.pause(0.6)
            assert not pane.running, "frida started in a panel that was gone"

            # The spawn is deferred a frame. Stopped inside that frame — which
            # is what an unplug does — there is nothing left to start.
            live = app.panels[0]
            pane = live.term
            pane.start(["sh", "-c", "sleep 31"])
            pane.stop()
            await pilot.pause(0.4)
            assert pane.proc is None and not pane.running, pane.proc
            assert not live.has_class("running"), "the layout was left in the running state"

            # And removed inside it: a removed widget answers True to
            # is_mounted for as long as it exists, so that was never the check.
            pane.start(["sh", "-c", "sleep 32"])
            await live.remove()
            await pilot.pause(0.4)
            assert pane.proc is None and not pane.running, pane.proc

            # Same for a stream: l asks the question, the cable comes out while
            # it is up, and the answer would start a logcat nobody can stop.
            live.start_stream("logcat", "sh", "-c", "sleep 33")
            await pilot.pause(0.4)
            assert not live.streams, live.streams

            # A codeshare fetch outliving its screen, both ways: the page that
            # arrives after the dismissal, and the failure that arrives after it.
            (TMP / "netslow").touch()
            try:
                for down in (False, True):
                    if down:
                        (TMP / "netdown").touch()
                    app.push_screen(moabile.CodeshareScreen())
                    assert await on_screen(pilot, app, moabile.CodeshareScreen), app.screen
                    app.pop_screen()
                    for _ in range(60):          # past the fake's own sleep
                        await pilot.pause(0.05)
            finally:
                (TMP / "netslow").unlink()
                (TMP / "netdown").unlink(missing_ok=True)
    finally:
        (TMP / "frida-up").unlink(missing_ok=True)
    print("PASS a panel or a screen that goes away mid-await takes nothing with it")


async def _async_tuple(v: tuple[int, str]) -> tuple[int, str]:
    return v


async def _async_str(v: str) -> str:
    return v


async def _async_bool(v: bool) -> bool:
    return v


async def _async_none() -> None:
    return None


async def _async_obj(v: object) -> object:
    return v


class StubPanel(moabile.DevicePanel):
    async def copy_in(self, local: str, remote: str) -> tuple[int, str]: return 0, "ok"
    @property
    def can_stage(self) -> bool: return True
    async def pull(self, remote: str, local: str) -> tuple[int, str]: return 0, "ok"
    async def describe(self) -> None: pass
    async def load_packages(self) -> None: pass
    async def stats(self) -> dict[str, str]: return {}
    async def system_info(self) -> None: pass
    async def install(self, path: str) -> tuple[int, str]: return 0, "ok"
    async def existing_exports(self, dest: str) -> list[Path]: return []
    async def save_app(self, into: str) -> None: pass
    async def shell_argv(self) -> tuple[list[str], str]: return ["sh"], ""
    def mirror_argv(self, port: int) -> list[str]: return ["mirror"]
    async def log_command(self, pid: str) -> list[str]: return ["log"]
    async def app_pid(self) -> str | None: return None
    async def launch_app(self) -> bool: return True
    def server_arch(self) -> str | None: return "arm64"
    async def server_files(self, ver: str, arch: str) -> list[tuple[Path, str]] | None: return []


async def test_edge_cases() -> None:
    """Exercise abstract base classes, error handlers, and boundary paths."""
    # 1. Non-existent command & echo_off
    rc, out = await moabile.sh("/nonexistent_tool_12345", timeout=1)
    assert rc == 127
    assert moabile.echo_off(-1) is False

    # 2. LogoScreen events
    logo = moabile.LogoScreen()
    logo.on_key(events.Key("enter", "enter"))
    logo.on_mouse_down(events.MouseDown(None, 0, 0, 0, 0, 1, False, False, False))

    # 3. FileList abstract methods
    fl = moabile.FileList("/tmp")
    for m, a in [
        (fl.listing, ()), (fl.delete, ("/tmp/f",)),
        (fl.rename, ("/tmp/a", "/tmp/b")), (fl.exists, ("f",)),
    ]:
        try:
            fn: Any = m
            await fn(*a)
        except NotImplementedError:
            pass

    # 4. HostList errors
    hl = moabile.HostList("/nonexistent_dir_9999")
    assert (await hl.listing())[0] != 0
    assert (await hl.delete("/nonexistent_dir_9999/f"))[0] != 0
    assert (await hl.rename("", ""))[0] != 0

    # 5. DevicePanel abstract & properties
    class FakeApp:
        def __init__(self) -> None:
            self.panels: list[object] = []

        def notify(self, *a: object, **kw: object) -> None: pass
        async def push_screen_wait(self, *a: object, **kw: object) -> object: return None
        def push_screen(self, *a: object, **kw: object) -> None: pass

    dp_raw = moabile.DevicePanel("dummy", cast(moabile.MOABile, FakeApp()))
    for m, a in [
        (dp_raw.copy_in, ("", "")),
        (dp_raw.pull, ("", "")),
        (dp_raw.describe, ()),
        (dp_raw.load_packages, ()),
        (dp_raw.stats, ()),
        (dp_raw.system_info, ()),
        (dp_raw.install, ("",)),
        (dp_raw.existing_exports, ("",)),
        (dp_raw.save_app, ("",)),
        (dp_raw.shell_argv, ()),
        (dp_raw.log_command, ("",)),
        (dp_raw.app_pid, ()),
        (dp_raw.launch_app, ()),
        (dp_raw.server_files, ("", "")),
    ]:
        try:
            fn = m
            await fn(*a)
        except NotImplementedError:
            pass

    try: _ = dp_raw.can_stage
    except NotImplementedError: pass
    try: _ = dp_raw.server_arch()
    except NotImplementedError: pass
    try: _ = dp_raw.mirror_argv(0)
    except NotImplementedError: pass

    dp: Any = StubPanel("dummy", cast(moabile.MOABile, FakeApp()))
    await dp.package_chosen()
    await dp.wake_app()
    assert await dp.data_dir() == ""
    assert await dp.frida_blocker() is None
    assert dp.summary() == ""
    assert dp.cpu == "?"
    assert moabile.VERSION == "1.1.1"

    # Log filter edge cases: case-insensitivity, history retention, regex escaping
    dp.log_history.clear()
    dp.log_filter = "warning"
    dp.write("info message")
    dp.write("a WARNING message")
    assert len(dp.log_history) == 2
    dp.log_filter = "[crash+*]"
    dp.write("[crash+*] occurred")
    dp.write("crash message")
    assert len(dp.log_history) == 4
    dp.log_filter = ""

    # TextViewerScreen actions
    tv = moabile.TextViewerScreen("Title", "line1\nline2")
    assert tv.title_text == "Title"
    assert tv.content_text == "line1\nline2"
    tv.dismiss = lambda r=None: setattr(tv, "_dismissed", True)
    tv.action_dismiss_viewer()
    assert getattr(tv, "_dismissed", False) is True

    # TerminalPane pause on exit
    tp = moabile.TerminalPane(dp)
    assert tp.exited is None
    tp.exited = 1
    tp.on_key(events.Key("enter", "enter"))
    assert tp.exited is None

    # Toggle frida when frida is up and kill fails with output
    dp.frida_pid = lambda: _async_str("9999")
    dp.run = lambda c: _async_tuple((1, "kill failed"))
    await dp.toggle_frida()
    dp.frida_pid = lambda: _async_none()

    # 6. DevicePanel push_as_root errors
    dp.copy_in = lambda l, r: _async_tuple((1, "err"))
    assert (await dp.push_as_root("l", "r")) == (1, "err")
    dp.copy_in = lambda l, r: _async_tuple((0, "ok"))
    dp.run = lambda c: _async_tuple((1, "mv failed"))
    assert (await dp.push_as_root("l", "r"))[0] == 1

    # 7. DevicePanel ensure_frida error branches
    dp.frida_pid = lambda: _async_none()
    dp.frida_blocker = lambda: _async_none()
    sh_orig = moabile.sh
    moabile.sh = lambda *a, **kw: _async_tuple((0, "no version")) if a[0] == "frida" else sh_orig(*a, **kw)
    try:
        assert await dp.ensure_frida() is False
    finally:
        moabile.sh = sh_orig

    dp.server_arch = lambda: None
    assert await dp.ensure_frida() is False

    dp.server_arch = lambda: "arm64"
    dp.server_files = lambda v, a: _async_none()
    dp.server_bytes = lambda: _async_none()
    assert await dp.ensure_frida() is False

    tfile = Path(TMP) / "dummy_local_test"
    tfile.write_text("x")
    dp.mob.push_screen_wait = lambda s: _async_bool(True)
    dp.server_files = lambda v, a: _async_obj([(tfile, "/remote")])
    dp.push = lambda l, r: _async_tuple((1, "push failed"))
    assert await dp.ensure_frida() is False

    dp.push = lambda l, r: _async_tuple((0, "ok"))
    dp.run = lambda c, **kw: _async_tuple((0, "ok"))
    dp.launch_server = lambda w: _async_bool(False)
    assert await dp.ensure_frida() is False
    tfile.unlink(missing_ok=True)

    # ensure_frida custom version choice when no server on device
    dp.mob.push_screen_wait = lambda s: (
        _async_str("c") if isinstance(s, moabile.ConfirmScreen)
        else _async_str("16.2.1")
    )
    dp.server_files = lambda v, a: _async_none()
    assert await dp.ensure_frida() is False

    # launch_server testing: success, error log, and fallback
    dp.launch_server = moabile.DevicePanel.launch_server.__get__(dp, moabile.DevicePanel)
    dp.server_path = "/server"
    dp.frida_pid = lambda: _async_str("5432")
    assert await dp.launch_server("frida-server") is True

    dp.frida_pid = lambda: _async_none()
    dp.run = lambda c, **kw: (
        _async_tuple((0, "Unable to bind to address: Address already in use"))
        if "cat " in c else _async_tuple((0, "ok"))
    )
    assert await dp.launch_server("frida-server") is False

    dp.run = lambda c, **kw: _async_tuple((0, ""))
    assert await dp.launch_server("frida-server") is False

    # 8. warn_drift
    dp.warn_drift = moabile.DevicePanel.warn_drift.__get__(dp, moabile.DevicePanel)
    dp.frida_platform = "android"
    dp.server_path = "/server"
    dp.frida_pid = lambda: _async_str("123")
    dp.run = lambda c: _async_tuple((0, "frida-server-12.0.0"))
    moabile.sh = lambda *a, **kw: _async_tuple((0, "16.5.9")) if a[0] == "frida" else sh_orig(*a, **kw)
    try:
        await dp.warn_drift()
    finally:
        moabile.sh = sh_orig

    # 9. prune_cache with stale dir
    stale_dir = moabile.CACHE / "frida-stale-test"
    stale_dir.mkdir(parents=True, exist_ok=True)
    dp.prune_cache("16.5.9")
    assert not stale_dir.exists()

    # 10. start_stream with OSError
    dp.start_stream("fail_stream", "/nonexistent_cmd_xyz_123")

    # 11. AndroidPanel cat_out and save_app errors
    ap: Any = moabile.AndroidPanel("emulator-5554", cast(moabile.MOABile, FakeApp()))
    ap.root = True
    ap.props = {"ro.product.device": "pixel"}
    await ap.cat_out("/sdcard/test.txt", str(TMP))
    orig_sh = moabile.sh
    moabile.sh = lambda *a, **kw: _async_tuple((124, "timed out"))
    try:
        await ap.cat_out("/sdcard/test.txt", str(TMP))
    finally:
        moabile.sh = orig_sh
    ap.package = "com.test.app"
    ap.adb = lambda *a, **kw: _async_tuple((1, ""))
    await ap.save_app(str(TMP))
    ap.adb = lambda *a, **kw: _async_tuple((0, "package:/data/app/test.apk"))
    ap.pull = lambda l, r: _async_tuple((1, "err"))
    await ap.save_app(str(TMP))
    target_apk = Path(TMP) / "com.test.app-test.apk"
    target_apk.touch()
    try:
        assert len(await ap.existing_exports(str(TMP))) == 1
    finally:
        target_apk.unlink(missing_ok=True)

    # unpack_deb with dir entry
    dir_info = tarfile.TarInfo("dir/")
    dir_info.type = tarfile.DIRTYPE
    inner_tar = io.BytesIO()
    with tarfile.open(fileobj=inner_tar, mode="w") as tar:
        tar.addfile(dir_info)
    trap_deb = Path(TMP) / "dummy_dir.deb"
    trap_deb.write_bytes(b"!<arch>\n" + ar_member("data.tar", inner_tar.getvalue()))
    assert moabile.unpack_deb(trap_deb, Path(TMP) / "out_dir") == []
    trap_deb.unlink(missing_ok=True)
    shutil.rmtree(Path(TMP) / "out_dir", ignore_errors=True)

    # 12. IosPanel error branches
    ios: Any = moabile.IosPanel("00008030001122334455667788AABBCC", cast(moabile.MOABile, FakeApp()))
    ios.props = {}
    assert await ios.wifi_address() is None
    ios.props = {"WiFiAddress": "aa:bb:cc:dd:ee:ff"}
    orig_sh = moabile.sh
    moabile.sh = lambda *a, **kw: _async_tuple((
        0, ("192.168.1.1 dev eth0 lladdr 11:22:33:44:55:66 REACHABLE\n"
            "192.168.1.105 dev eth0 lladdr aa:bb:cc:dd:ee:ff REACHABLE\n"),
    ))
    assert await ios.wifi_address() == "192.168.1.105"
    moabile.sh = orig_sh
    ios.root = False
    assert "frida-server needs root" in (await ios.frida_blocker() or "")

    moabile.sh = lambda *a, **kw: _async_tuple((0, "Complete\niTunesMetadata.plist missing")) if "ideviceinstaller" in a else sh_orig(*a, **kw)
    try:
        rc, out = await ios.install("/path/to/app.ipa")
        assert "iTunesMetadata" in out
    finally:
        moabile.sh = sh_orig

    ios.package = "com.target.ios"
    ios.bundle_dir = lambda: _async_str("/var/containers/Bundle/Application/uuid/Target.app")
    ios.pull = lambda l, r: _async_tuple((0, "ok"))
    target_ipa = Path(TMP) / "com.target.ios.ipa"
    target_ipa.touch()
    try:
        assert len(await ios.existing_exports(str(TMP))) == 1
        orig_make = shutil.make_archive
        def fail_archive(*a: object, **kw: object) -> str: raise OSError("No space")
        shutil.make_archive = fail_archive
        try:
            await ios.save_app(str(TMP))
        finally:
            shutil.make_archive = orig_make
    finally:
        target_ipa.unlink(missing_ok=True)

    ios.mob.push_screen_wait = lambda scr: _async_str("invalid/login")
    await ios.set_login()

    ios.package = None
    assert await ios.dir_holding("/var/plists") == ""

    # Prefix collision: grep regex must target the exact package identifier
    calls: list[str] = []
    ios.package = "app.com.1"
    ios.run = lambda cmd, **kw: (calls.append(cmd), _async_tuple((0, "/var/containers/Bundle/Application/AA/App.app/Info.plist\n")))[1]  # type: ignore[assignment]
    res = await ios.dir_holding("/var/plists")
    assert res == "/var/containers/Bundle/Application/AA/App.app", res
    assert len(calls) == 1
    assert "app\\.com\\.1([^A-Za-z0-9_.-]|$)" in calls[0], calls[0]

    # Real plist grep test (both binary and XML formats) with prefix collision
    import plistlib
    f_short = Path(TMP) / "short.plist"
    f_long = Path(TMP) / "long.plist"
    for fmt in (plistlib.FMT_BINARY, plistlib.FMT_XML):
        f_short.write_bytes(plistlib.dumps({"CFBundleIdentifier": "app.com.1"}, fmt=fmt))
        f_long.write_bytes(plistlib.dumps({"CFBundleIdentifier": "app.com.1.test"}, fmt=fmt))
        pattern = f"{re.escape('app.com.1')}([^A-Za-z0-9_.-]|$)"
        rc, out = await moabile.sh("sh", "-c", f"grep -lsE {shlex.quote(pattern)} {f_short} {f_long} 2>/dev/null")
        assert rc == 0 and out.strip().splitlines() == [str(f_short)], (fmt, out)
    f_short.unlink(missing_ok=True)
    f_long.unlink(missing_ok=True)

    ios.run = lambda *a, **kw: _async_tuple((1, "some grep error"))
    await ios.dir_holding("/var/plists")

    ios.prune_cache = lambda ver: None
    ios.download = lambda *a, **kw: _async_bool(True)
    orig_unpack = moabile.unpack_deb
    moabile.unpack_deb = lambda *a, **kw: []
    deb_p = moabile.CACHE / "dummy_frida.deb"
    deb_p.parent.mkdir(parents=True, exist_ok=True)
    deb_p.write_bytes(b"dummy")
    try:
        assert await ios.server_files("16.5.9", "arm64") is None
    finally:
        moabile.unpack_deb = orig_unpack
        deb_p.unlink(missing_ok=True)

    # FileList abstract methods
    try: fl.title()
    except NotImplementedError: pass

    try: str(dp_raw)
    except NotImplementedError: pass
    await dp.refresh_stats()

    # TerminalPane ctrl character & stop
    term_pane: Any = moabile.TerminalPane(dp)
    term_pane.proc = type("Proc", (), {"pid": 1234, "poll": lambda s: None, "wait": lambda s, timeout=2: None})()
    r_fd, w_fd = os.pipe()
    os.close(w_fd)
    term_pane.fd = r_fd
    term_pane.on_key(events.Key("ctrl+c", "c"))
    term_pane.stop()

    # IosPanel remaining branches
    orig_free = moabile.port_free
    moabile.port_free = lambda port: False
    try:
        assert ios.pick_port() == 0
    finally:
        moabile.port_free = orig_free

    ios.master_said = False
    assert (await ios.open_master("")) != ""

    ios.ssh_user = "root"
    # Restored first: ios.run is still the line-1185 stub here, which swallows
    # any keyword and would hide a wrong one (`root`, not `as_root`) for good.
    # master_up mocked before calling it for real: this ios is a standalone
    # object nothing ever tears down, and the real one opens a genuine usb
    # tunnel on a real local port that would then sit there for the rest of
    # the run, taking IOS_SSH_PORT away from the ios panel phase_ios opens.
    ios.run = moabile.IosPanel.run.__get__(ios, moabile.IosPanel)
    ios.master_up = lambda: _async_bool(False)
    await ios.run("id", root=True)
    ios.pull = moabile.IosPanel.pull.__get__(ios, moabile.IosPanel)
    assert (await ios.scp("l", "r"))[0] != 0
    assert (await ios.pull("r", "l"))[0] != 0

    ios.bundle_dir = lambda: _async_none()
    await ios.package_chosen()

    ios.bundle_dir = lambda: _async_str("bundle")
    ios.pull = lambda l, r: _async_tuple((1, "pull error"))
    await ios.save_app(str(TMP))

    ios.mob.push_screen_wait = lambda scr: _async_none()
    await ios.set_login()

    ios.download = lambda *a, **kw: _async_bool(False)
    assert await ios.server_files("16.5.9", "arm64") is None

    deb_p = moabile.CACHE / "dummy_frida.deb"
    deb_p.parent.mkdir(parents=True, exist_ok=True)
    deb_p.write_bytes(b"dummy")
    ios.download = lambda *a, **kw: _async_bool(True)
    def fail_unpack(*a: object, **kw: object) -> list[str]: raise tarfile.TarError("bad archive")
    moabile.unpack_deb = fail_unpack
    try:
        assert await ios.server_files("16.5.9", "arm64") is None
    finally:
        moabile.unpack_deb = orig_unpack
        deb_p.unlink(missing_ok=True)

    # Test copy_to_clipboard on MOABile
    app_cli = moabile.MOABile()
    app_cli.copy_to_clipboard("test_text")
    assert app_cli._clipboard == "test_text"

    # Test server_files with a deb having frida-1.0 layout
    inner_tar = io.BytesIO()
    with tarfile.open(fileobj=inner_tar, mode="w") as tar:
        for fname in ("./var/jb/usr/sbin/frida-server", "./var/jb/usr/lib/frida-1.0/frida-agent.dylib"):
            info = tarfile.TarInfo(fname)
            info.size = 10
            tar.addfile(info, io.BytesIO(b"0123456789"))
    deb_17 = moabile.CACHE / "frida_17.17.0_iphoneos-arm64.deb"
    deb_17.parent.mkdir(parents=True, exist_ok=True)
    deb_17.write_bytes(b"!<arch>\n" + ar_member("data.tar", inner_tar.getvalue()))
    unpacked_17 = moabile.CACHE / "frida-17.17.0-iphoneos-arm64"
    shutil.rmtree(unpacked_17, ignore_errors=True)
    files_17 = await ios.server_files("17.17.0", "arm64")
    assert files_17 is not None
    remotes = [r for _l, r in files_17]
    assert any("frida-1.0/frida-agent.dylib" in r for r in remotes), remotes
    deb_17.unlink(missing_ok=True)
    shutil.rmtree(unpacked_17, ignore_errors=True)

    print("PASS edge cases: error paths, base classes, and process boundaries")


async def test_stress() -> None:
    """Hammer the bindings in a random order while the status poll runs.

    Toggles that race each other are how half the bugs in this file were found:
    a pane started twice, a view stopped mid-frame, a panel closed under a poll.

    With an app selected, and with y, n and escape in the pool: half the keys
    put a question up first — which of the two logs, whether to attach or
    spawn, whether to take frida-server off the device — and a run that never
    answers one spends the rest of itself inside a modal, hammering nothing.
    """
    random.seed(11)
    app = moabile.MOABile()
    async with app.run_test() as pilot:
        assert await on_screen(pilot, app, moabile.DepsScreen)
        await pilot.press("enter")
        assert await settle(pilot, lambda: bool(app.panels), tries=200)
        devices = app.query_one("#devices", ListView)
        packages = app.query_one("#packages", ListView)
        # An app selected: most of what these keys reach — the log filter, the
        # attach question, the pid in the stats line — needs one.
        assert await settle(pilot, lambda: len(packages._nodes) > 1, tries=200), \
            len(packages._nodes)
        select(packages, "com.target.app")
        assert await settle(pilot, lambda: any(p.package for p in app.panels), tries=200), \
            [p.package for p in app.panels]
        # And as if the app were up: the attach question, the log's pid filter
        # and the pid in the stats line all hang off there being a pid to find,
        # so without this the keys walk straight past the half of the code that
        # only runs when an app is running.
        running = [TMP / f"running-{serial}"
                   for serial in ("emulator-5554", "emulator-5556")]
        for flag in running:
            flag.touch()
        # Every key the bar has, less two: q asks to quit and would end the
        # run, and v writes an svg wherever the process happens to be standing.
        # The rest open modals over each other on purpose — y, n and escape are
        # in the pool so they get answered rather than piling up.
        keys = [b.key for b in moabile.MOABile.BINDINGS
                if isinstance(b, moabile.Binding) and b.key not in ("q", "v")]
        keys += ["y", "n", "escape"]
        try:
            for i in range(200):
                await pilot.press(random.choice(keys))
                if i % 17 == 0 and devices._nodes:
                    devices.index = random.randrange(len(devices._nodes))
                    devices.action_select_cursor()
                if i % 5 == 0:
                    await pilot.pause(0.02)
        finally:
            for flag in running:                 # the phases below start it themselves
                flag.unlink(missing_ok=True)
        await pilot.pause(0.5)
        for panel in app.panels:
            await panel.shutdown()
    # run_test re-raises anything a worker threw, so reaching here is the result.
    print("PASS 200 random actions in a row leave the app standing")


async def test_gate() -> None:
    """A missing tool has to be installed before the app will let anyone in."""
    app = moabile.MOABile()
    async with app.run_test() as pilot:
        assert await on_screen(pilot, app, moabile.DepsScreen)
        screen = cast(moabile.DepsScreen, app.screen)
        # Neither family complete: android is a scrcpy short, ios an ioscpy.
        assert [t.name for t in screen.missing] == ["scrcpy", "ioscpy"], screen.missing
        assert screen.blocked and screen.ready == [], screen.ready
        # No install commands in the hints: the package manager and the package
        # name are the host's business and both drift, so a row names the project.
        assert not [t for t in screen.tools
                    if any(w in t.source for w in ("install", "apt", "brew", "dnf",
                                                   "pacman", "pipx", "pkg"))], \
            [t.source for t in screen.tools]
        assert all(t.why for t in screen.tools), "a tool that does not say what it is for"
        await pilot.press("enter")
        # The gate re-checks and pushes a fresh screen, so wait for that rather
        # than for a fixed delay.
        assert await on_screen(pilot, app, moabile.DepsScreen), app.screen
        screen = cast(moabile.DepsScreen, app.screen)
        assert screen.blocked, "enter got past the gate"
        assert not app.panels, "the app started with no usable family"

        # Answers --version at once, otherwise stays up like the real window.
        fake("scrcpy", '[[ "$*" == "--version" ]] && { echo "scrcpy 2.4"; exit 0; }\nsleep 40')
        await pilot.press("r")
        # One complete family is enough to get in, even with the other short.
        assert await settle(pilot, lambda: not cast(moabile.DepsScreen, app.screen).blocked), "recheck did not clear it"
        screen = cast(moabile.DepsScreen, app.screen)
        assert screen.ready == ["android"], screen.ready
        assert [t.name for t in screen.missing] == ["ioscpy"], screen.missing
        fake("ioscpy", '[[ "$*" == "--version" ]] && { echo "ioscpy 1.0.3"; exit 0; }\nsleep 40')
        await pilot.press("r")
        assert await settle(pilot, lambda: not cast(moabile.DepsScreen, app.screen).missing), "recheck did not clear it"
        screen = cast(moabile.DepsScreen, app.screen)
        # Just the number: "scrcpy 2.4" and "Android Debug Bridge version
        # 1.0.41" both say the name, which the row already has.
        found = {t.name: t.version for t in screen.tools}
        assert found["scrcpy"] == "2.4" and found["adb"] == "1.0.41", found
        assert all(re.fullmatch(r"[\d.]+", v) for v in found.values()), found
        assert found["objection"] == "1.11.0" and found["curl"] == "8.5.0", found
        await pilot.press("enter")
        assert await settle(pilot, lambda: bool(app.panels)), "gate did not open once satisfied"
        assert app.ready == ["android", "ios"], app.ready
    print("PASS startup gate blocks until a whole device family is installed")


async def phase_devices(app, pilot) -> None:
    """panels, the sidebar, and per-panel selection."""
    a, b = app.panels
    assert (a.serial, b.serial) == ("emulator-5554", "emulator-5556")
    # The model carries "[/]": unescaped, that markup crashes Static.update
    # and takes the panel with it, the way logcat lines once did.
    assert a.props["ro.product.model"] == "Pixel 4 [/] [bold]", a.props["ro.product.model"]
    # The model carries "[/]": the border renders markup, so it has to arrive
    # escaped or a device name would take the panel down.
    assert "Pixel 4" in a.border_title and "\\[/]" in a.border_title, a.border_title
    # The codename beside the model: it is what the shell prompt says too.
    assert a.border_title.endswith("· emu64x"), a.border_title
    assert "android 13 · api 33" in a.border_subtitle, a.border_subtitle
    # The unrooted device says so in its own border, the rooted one does not.
    assert "no root" in a.border_subtitle and "no root" not in b.border_subtitle, \
        (a.border_subtitle, b.border_subtitle)
    assert a.root is False and b.root is True, (a.root, b.root)
    print("PASS a panel opens per device; props and root read per device")

    side = app.query_one("#side")
    await pilot.press("b")
    await pilot.pause()
    assert side.display is False, "b did not hide the sidebar"
    await pilot.press("b")
    await pilot.pause()
    assert side.display is True, "b did not bring the sidebar back"
    print("PASS b hides and restores the sidebar")

    # The apps of the active device live at the foot of the sidebar, clear of
    # the device rows: stacked flush under them the second list read as more
    # of the first.
    devices, apps = app.query_one("#devices"), app.query_one("#apps")
    assert apps.region.bottom == side.region.bottom, (apps.region, side.region)
    assert apps.region.y > devices.region.bottom, (apps.region, devices.region)
    # The filter is a field, so it has to have a ground of its own. $boost —
    # what this used to ask for — is transparent in any theme that names its
    # own panel colour, which both of these do, so the field was a stray line
    # of text on the sidebar's own background.
    field = app.query_one("#filter", Input)
    assert field.background_colors[1] != side.background_colors[1], \
        (field.background_colors[1].hex, side.background_colors[1].hex)
    print("PASS the app list sits at the foot of the sidebar, not under the devices")

    def active_rows() -> list[str]:
        return [row.value for row in app.query_one("#devices", ListView).query(moabile.ValueItem)
                if row.has_class("-active")]

    # Two panels are open and only one of them is listening: the row for it
    # says which, and moving between panels moves the mark.
    a.focus()
    await pilot.pause()
    assert active_rows() == [a.serial], active_rows()
    b.focus()
    await pilot.pause()
    assert active_rows() == [b.serial], active_rows()
    # And the mark is one that can be seen: the row is the accent colour and
    # bold where every other row is the plain foreground. A class whose rule
    # paints nothing is exactly the trap $boost was.
    rows = list(app.query_one("#devices", ListView).query(moabile.ValueItem))
    marked = next(r for r in rows if r.has_class("-active"))
    plain = next(r for r in rows if not r.has_class("-active"))
    here = app.screen.get_style_at(3, marked.region.y)
    there = app.screen.get_style_at(3, plain.region.y)
    assert here.bold and here.color != there.color, (here, there)
    print("PASS the device list marks which device the keys are about")

    a.focus()
    await pilot.pause()
    select(app.query_one("#packages", ListView), "com.target.app")
    assert await settle(pilot, lambda: a.package == "com.target.app", tries=120), a.package
    assert b.package is None, "package selection leaked to the other panel"
    # The pid only appears once the stats poll has run with a package set.
    assert await settle(pilot, lambda: "4242" in _stats(a), tries=120), _stats(a)
    stats = _stats(a)
    # GB, so the line still fits a panel narrowed by a second one beside it.
    assert "2.5/4.0 GB" in stats, stats
    assert "uid" not in stats, "uid is back in the stats line"
    assert "192.168.1.44" in stats, stats

    # A device that answered and has no network reads `usb`, not `?` — the same
    # answer the ios side gives for the same reason, and `?` is kept for the
    # reading that never happened at all. `adb connect` puts the address in the
    # serial, and then that is the address.
    (TMP / "noroute").touch()
    try:
        assert (await a.stats())["ip"] == "usb", await a.stats()
        was, a.serial = a.serial, "192.168.1.9:5555"
        assert (await a.stats())["ip"] == "192.168.1.9", await a.stats()
        a.serial = was
        assert a.address({}) == "?", a.address({})
    finally:
        (TMP / "noroute").unlink()
    assert (await a.stats())["ip"] == "192.168.1.44", await a.stats()
    print("PASS the address row reads usb on both families, and ? only when unasked")

    # Clicking into the sidebar takes focus out of every panel. Deriving the
    # active panel from focus alone silently fell back to the first one.
    b.focus()
    await pilot.pause()
    app.query_one("#packages", ListView).focus()
    await pilot.pause()
    assert app.active is b, f"sidebar focus stole the active panel: {app.active}"
    select(app.query_one("#packages", ListView), "com.target.app")
    assert await settle(pilot, lambda: b.package == "com.target.app"), (a.package, b.package)
    pkg_rows = list(app.query_one("#packages", ListView).query(moabile.ValueItem))
    assert next(r for r in pkg_rows if r.has_class("-active")).value == "com.target.app"
    # The sidebar says how much of the list the filter is hiding.
    head = app.query_one("#pkghead")
    assert "2/2" in str(head.render()), str(head.render())
    # The apps installed on the device and not the system's own: -3, which is
    # the half the ios side asks for too.
    assert "com.android.settings" not in b.packages, b.packages
    assert "pm list packages -3" in (TMP / "adb-log").read_text(), "the whole device was listed"
    app.query_one("#filter", Input).value = "target"
    assert await settle(pilot, lambda: "1/2" in str(head.render())), str(head.render())
    app.query_one("#filter", Input).value = ""
    assert await settle(pilot, lambda: "2/2" in str(head.render())), str(head.render())
    # Android is reached over adb: u has nothing to ask for, and says so
    # instead of doing nothing at all.
    b.focus()
    await pilot.pause()
    await pilot.press("u")
    assert await settle(pilot, lambda: "needs no login" in log_text(b)), log_text(b)
    print("PASS selection is per-panel and follows the active panel")
    print("PASS u has nothing to ask for on android, and says so")


async def phase_sidebar_cost(app, pilot) -> None:
    """the package list is rebuilt only when it would come out different."""
    b = app.panel("emulator-5556")
    b.focus()
    await pilot.pause()
    lv, head = app.query_one("#packages", ListView), app.query_one("#pkghead")
    # (no app) plus the two the fake pm lists.
    assert await settle(pilot, lambda: len(lv._nodes) == 3), len(lv._nodes)

    # Picking a package redraws the sidebar. Rebuilding the list to the same
    # rows costs a widget mount each and drops the cursor back to the top.
    was, index = list(lv._nodes), lv.index
    select(lv, "com.other.app")
    assert await settle(pilot, lambda: b.package == "com.other.app"), b.package
    assert list(lv._nodes) == was, "the package list was rebuilt under the cursor"
    assert lv.index != index and lv.index is not None, "the cursor moved back to the top"

    # Typing updates the count at once and the rows on a timer, so a keystroke
    # never pays a mount per package.
    app.show_packages("target", rows=False)
    assert "1/2" in str(head.render()), str(head.render())
    assert len(lv._nodes) == 3, "rows=False rebuilt the list anyway"
    app.query_one("#filter", Input).value = "target"
    assert await settle(pilot, lambda: len(lv._nodes) == 2), len(lv._nodes)
    app.query_one("#filter", Input).value = ""
    assert await settle(pilot, lambda: len(lv._nodes) == 3), len(lv._nodes)
    select(lv, "com.target.app")
    assert await settle(pilot, lambda: b.package == "com.target.app"), b.package

    # When focused, the selected package row has -highlight and -active; its label
    # color must resolve to $background (dark) instead of $accent (orange), avoiding
    # orange-on-orange invisible text.
    active_row = next(r for r in lv.query(moabile.ValueItem) if r.value == "com.target.app")
    assert active_row.has_class("-active")
    lv.focus()
    await pilot.pause()
    bg_color = Color.parse(moabile.DARK.background)
    assert active_row.query_one(moabile.Label).styles.color == bg_color
    b.focus()
    await pilot.pause()
    assert active_row.query_one(moabile.Label).styles.color != bg_color

    # Every row is a widget mount, and a phone with a couple of hundred apps on
    # it paid that on every pause in the filter — the field lagged behind the
    # typing. The drawing is capped and the head says so; the count itself
    # stays the whole truth, or an app past the cap would read as one that is
    # not installed at all.
    kept = b.packages
    b.packages = [f"com.example.app{n:03d}" for n in range(moabile.PACKAGE_ROWS + 60)]
    app.show_packages("")
    assert await settle(pilot, lambda: len(lv._nodes) == moabile.PACKAGE_ROWS + 1,
                        tries=200), len(lv._nodes)
    drawn = str(head.render())
    assert f"{moabile.PACKAGE_ROWS + 60}/{moabile.PACKAGE_ROWS + 60}" in drawn, drawn
    assert f"{moabile.PACKAGE_ROWS} shown" in drawn, drawn
    b.packages = kept
    app.show_packages("")
    assert await settle(pilot, lambda: len(lv._nodes) == 3), len(lv._nodes)
    assert "shown" not in str(head.render()), str(head.render())
    print("PASS the package list is rebuilt only when it changed")
    print("PASS a list too long to mount is capped, and the count still says how many")


async def phase_keys(app, pilot) -> None:
    """the key bar, the help panel, and the two themes."""
    # No command palette: the bar is the only list of commands, so ctrl+p must
    # not open anything and every key in the bar has to be one of ours.
    assert app.ENABLE_COMMAND_PALETTE is False, "the palette is back"
    await pilot.press("ctrl+p")
    await pilot.pause(0.2)
    assert type(app.screen).__name__ != "CommandPalette", app.screen
    shown = [(key.key, key.description) for key in app.query(FooterKey)]
    declared = [(b.key, b.description) for b in moabile.MOABile.BINDINGS if isinstance(b, moabile.Binding) and b.show]
    assert shown and shown == declared[:len(shown)], (shown, declared)
    assert all("palette" not in description for _key, description in shown), shown
    print("PASS the key bar is the only list of commands, and ctrl+p opens nothing")

    # b and h are not in the scrolling part of the bar: they are pinned to its
    # ends, so a terminal too narrow for nineteen keys can never cut off the
    # one key that lists the rest.
    assert not any(key in ("b", "h") for key, _ in shown), shown
    bar = app.query_one("#bar")
    pinned = list(bar.query(moabile.BarKey))
    assert [key.key for key in pinned] == ["b", "h"], pinned
    assert (bar.children[0], bar.children[-1]) == (pinned[0], pinned[1]), bar.children
    assert pinned[0].region.x == bar.region.x, (pinned[0].region, bar.region)
    assert pinned[1].region.right == bar.region.right, (pinned[1].region, bar.region)
    # Worded by the binding, not by a second copy of its words.
    assert "sidebar" in str(pinned[0].render()) and "help" in str(pinned[1].render()), pinned

    # And clickable, the way the keys between them are.
    side = app.query_one("#side")
    await pilot.click(pinned[0])
    assert await settle(pilot, lambda: side.display is False), "clicking b did nothing"
    await pilot.click(pinned[0])
    assert await settle(pilot, lambda: side.display is True), "clicking b left it hidden"
    print("PASS b and h are pinned to the ends of the bottom row, and click")

    assert app.theme == "moabile-dark", app.theme
    # Both themes are the app's own: a Textual release is free to change what
    # its built-ins look like, and the light built-in is white at full brightness.
    assert set(app.available_themes) == {"moabile-dark", "moabile-light"}, app.available_themes
    light = app.available_themes["moabile-light"]
    assert light.dark is False, light
    # Well under white, or it is the glare this theme exists to avoid.
    assert max(int(light.background.lstrip("#")[i:i + 2], 16) for i in (0, 2, 4)) < 0xE0, \
        light.background
    await pilot.press("m")
    assert await settle(pilot, lambda: app.theme == "moabile-light"), app.theme
    await pilot.press("m")
    assert await settle(pilot, lambda: app.theme == "moabile-dark"), app.theme
    print("PASS one dark mode, one light mode, dark by default, m switches")

    await pilot.press("h")
    assert await settle(pilot, lambda: bool(app.screen.query("HelpPanel"))), "no help panel"
    # Every key, including the two the bar does not show: the panel drops
    # Textual's own bindings and keeps ours whether they are in the bar or not,
    # and it is the only place b and h are written down.
    listed = Console(width=80, no_color=True)
    with listed.capture() as caught:
        listed.print(app.screen.query_one("BindingsTable").render_bindings_table())
    rows = caught.get()
    assert all(f"{b.key} " in rows or f" {b.description}" in rows
               for b in moabile.MOABile.BINDINGS if isinstance(b, moabile.Binding)), rows
    assert "sidebar" in rows and "help" in rows, rows
    await pilot.press("h")
    assert await settle(pilot, lambda: not app.screen.query("HelpPanel")), "help panel stuck open"

    # Where the SVG lands is Textual's business; that the key reaches it is ours.
    delivered: list[object] = []
    app.deliver_screenshot = lambda *a, **kw: delivered.append(a)
    await pilot.press("v")
    assert await settle(pilot, lambda: bool(delivered), tries=120), "v took no screenshot"
    print("PASS keys, screenshot and theme each have a key of their own")

    # Boxes are a share of the screen with a ceiling, so a narrow terminal
    # gets a popup with its border intact instead of a full-screen page.
    # FridaArgsScreen first, deliberately: it inherits its CSS, and Textual
    # registers a stylesheet per pushed class — so it used to open unstyled
    # unless a plain AskScreen had been shown before it.
    for maker in (lambda: moabile.FridaArgsScreen("t", "v"), lambda: moabile.AskScreen("t", "v"),
                  lambda: moabile.ConfirmScreen("q", "y", "n"), lambda: moabile.CodeshareScreen(),
                  lambda: moabile.ScriptScreen(str(TMP))):
        screen = maker()
        app.push_screen(screen)
        assert await settle(pilot, lambda screen=screen: bool(screen.query("#box"))), screen
        box = screen.query_one("#box")
        assert await settle(pilot, lambda box=box: box.size.width > 0), box.size
        outer = box.size.width + box.styles.border.spacing.width + box.styles.padding.width
        assert outer < app.size.width, (type(screen).__name__, outer, app.size.width)
        app.pop_screen()
        await pilot.pause()
    print("PASS every modal stays a bordered popup, never a full-screen page")


async def phase_tools(app, pilot) -> None:
    """the embedded terminal, objection and frida-client."""
    a, b = app.panels

    # The embedded pty: a program that prints, reads a line, and prints again.
    b.focus()
    await pilot.pause()
    b.term.start(["sh", "-c", "echo hello; read x; echo got:$x"])
    assert await settle(pilot, lambda: b.term.running), "process never spawned"
    assert await settle(pilot, lambda: "hello" in term_text(b)), term_text(b)
    assert b.term.running and b.has_class("running")
    for key in ("h", "i", "enter"):
        await pilot.press(key)
    assert await settle(pilot, lambda: not b.term.running), "process never reaped"
    assert not b.has_class("running"), "panel stayed in running layout"
    # What a tool prints stays in the tool's pane: dumping its last screen into
    # the panel log mixed a frida session into the record of what was run.
    assert "got:hi" not in log_text(b), log_text(b)
    assert "sh exited" in log_text(b), log_text(b)
    print("PASS terminal pane runs a program on a pty and forwards keys")

    # A program that exits non-zero pauses the pane so errors can be inspected.
    b.term.start(["sh", "-c", "echo 'fatal failure'; exit 2"])
    assert await settle(pilot, lambda: b.term.exited == 2, tries=200), b.term.exited
    assert b.term.running and b.has_class("running"), "pane closed instead of pausing on exit!=0"
    assert "exited with code 2" in b.term.border_subtitle, b.term.border_subtitle
    assert "fatal failure" in term_text(b), term_text(b)
    # c copies the error output and opens TextViewerScreen
    await pilot.press("c")
    assert await on_screen(pilot, app, moabile.TextViewerScreen, tries=200), app.screen
    assert "fatal failure" in app._clipboard
    await pilot.press("escape")
    assert await settle(pilot, lambda: not isinstance(app.screen, moabile.TextViewerScreen)), app.screen
    await pilot.press("enter")
    assert await settle(pilot, lambda: not b.term.running), "pane did not close on keypress"
    assert not b.has_class("running"), "panel stayed in running layout"
    assert "exited with 2 — pane kept open to inspect error" in log_text(b), log_text(b)
    # An intentional stop or ctrl-c (exit 130) closes cleanly without pausing
    b.term.start(["sh", "-c", "exit 130"])
    assert await settle(pilot, lambda: not b.term.running), "exit 130 paused instead of closing"
    print("PASS terminal pane stays open on non-zero exit until dismissed")

    # The log is the panel and a tool opens under it: what was run stays
    # readable while the REPL is up, instead of scrolling away behind it.
    order = [type(child).__name__ for child in b.children]
    assert order.index("RichLog") < order.index("TerminalPane"), order
    b.term.start(["sh", "-c", "echo both; sleep 20"])
    assert await settle(pilot, lambda: b.has_class("running")), b.has_class("running")
    assert b.term.region.height and b.query_one(RichLog).region.height, \
        (b.term.region, b.query_one(RichLog).region)
    b.term.stop()
    await pilot.pause()
    print("PASS the log stays visible under a running tool")

    # alt+c copies running terminal session without stopping the process
    b.term.start(["sh", "-c", "echo 'active terminal session'; sleep 20"])
    assert await settle(pilot, lambda: "active terminal session" in term_text(b)), term_text(b)
    await pilot.press("alt+c")
    assert await on_screen(pilot, app, moabile.TextViewerScreen, tries=200), app.screen
    assert "active terminal session" in app._clipboard
    await pilot.press("escape")
    assert await settle(pilot, lambda: not isinstance(app.screen, moabile.TextViewerScreen)), \
        app.screen
    assert b.term.running, "alt+c stopped the running terminal"
    # Scrollback history retains lines that scrolled off the visible screen
    for i in range(50):
        b.term.stream.feed(f"scrollback line {i}\r\n".encode())
    history = b.term.get_history_text()
    assert "scrollback line 0" in history and "scrollback line 49" in history, history
    b.term.stop()
    await pilot.pause()
    print("PASS alt+c copies running terminal session and scrollback retains lines")

    app.action_objection()
    await confirm(pilot, app, "y")
    assert await settle(pilot, lambda: b.term.argv[:1] == ["objection"], tries=300), b.term.argv
    assert (TMP / "monkey").exists(), "app was never started before attaching"
    # -g and explore are deprecated upstream; -n and start replace them. And -n
    # is the pid, not the package: objection resolves a name through frida's
    # application list, which carries a pid only for an app frida is already
    # holding — on a phone that is the difference between attaching and exit 1.
    assert b.term.argv == ["objection", "-S", "emulator-5556", "-n", "4242", "start"], b.term.argv
    # Which leaves the pane's border to say which app it is.
    assert "com.target.app" in b.term.label and "4242" in b.term.label, b.term.label
    print("PASS objection starts the app and attaches to its pid, in the panel")

    # An app with no launcher activity: monkey says so and exits 0 anyway, and
    # that sentence is the difference between "would not start" and knowing why.
    (TMP / "nolauncher").touch()
    (TMP / f"running-{b.serial}").unlink(missing_ok=True)
    assert not await b.launch_app(), "an app that cannot be started reported a launch"
    assert "No activities found" in log_text(b), log_text(b)
    # And o says so at once instead of watching the process table for ten
    # seconds: nothing here can start it, so there is nothing to wait for.
    began = time.monotonic()
    app.action_objection()
    assert await settle(pilot, lambda: "cannot be started from here" in log_text(b),
                        tries=200), log_text(b)
    assert time.monotonic() - began < 5, "waited for a launch that was never asked for"
    (TMP / "nolauncher").unlink()
    (TMP / f"running-{b.serial}").touch()
    print("PASS an app with no launcher activity says so, rather than not starting")

    (TMP / "frida-up").touch()
    app.action_frida_client()
    # The app is up from the objection test, so s asks which of the two it is.
    await confirm(pilot, app, "n")               # spawn it again
    assert await on_screen(pilot, app, moabile.FridaArgsScreen)
    app.screen.query_one("#answer", Input).value = 'a "unbalanced'
    await pilot.press("enter")
    assert await settle(pilot, lambda: "bad frida arguments" in log_text(b))
    print("PASS frida-client rejects unparsable arguments")

    # The spawn is deferred a frame, so a second press used to start a second
    # process and orphan the first, whose pty nobody would ever close.
    b.term.start(["sh", "-c", "sleep 31"])
    b.term.start(["sh", "-c", "sleep 32"])
    assert await settle(pilot, lambda: b.term.running), "nothing started"
    assert b.term.argv == ["sh", "-c", "sleep 31"], b.term.argv
    assert "already running" in log_text(b), log_text(b)
    b.term.stop()
    await pilot.pause()
    print("PASS a second start is refused while one is pending")

    # pyte's resize() wipes the screen, so a resize to the same size must be
    # a no-op or every repaint of the layout would erase the program output.
    b.term.start(["sh", "-c", "echo sized; sleep 20"])
    # Generous: this waits on a fork, a layout pass and a pty read.
    assert await settle(pilot, lambda: "sized" in term_text(b), tries=200), term_text(b)
    before = (b.term.vt.lines, b.term.vt.columns)
    b.term.on_resize()
    assert (b.term.vt.lines, b.term.vt.columns) == before
    assert "sized" in term_text(b), "a same-size resize wiped the screen"
    await pilot.resize_terminal(150, 45)
    assert await settle(pilot, lambda: (b.term.vt.lines, b.term.vt.columns) != before), before
    assert b.term.running, "the tool died on resize"
    b.term.stop()
    await pilot.pause()
    print("PASS the terminal pane resizes without wiping on a no-op")

    # A tool the system cannot run at all must be reported, not swallowed —
    # and in the panel's log is not enough when that panel is scrolled away.
    said: list[str] = []
    spoke, app.notify = app.notify, lambda message, **_kw: said.append(message)
    try:
        b.term.start(["/nonexistent/tool", "--go"])
        assert await settle(pilot, lambda: "/nonexistent/tool" in log_text(b)), log_text(b)
        assert any("/nonexistent/tool" in note for note in said), said
    finally:
        app.notify = spoke
    assert not b.term.running and not b.has_class("running")
    print("PASS a tool that cannot be executed is reported, on screen too")

    # f8 hands the keyboard back without killing what is running: every other
    # key belongs to the child process, ctrl+c included.
    b.term.start(["sh", "-c", "sleep 25"])
    assert await settle(pilot, lambda: b.term.running, tries=200), "nothing started"
    # settle, not a bare assert: focus goes through the message loop, so the
    # frame that sees the process running is not always the one holding it yet.
    assert await settle(pilot, lambda: b.term.has_focus), "the pane did not take the keyboard"
    assert app.query_one("#barkey-b").display is False
    assert app.query_one("#barkey-h").display is False
    assert app.check_action("quit", ()) is False
    assert app.check_action("copy_terminal", ()) is True
    assert app.check_action("leave_terminal", ()) is True
    await pilot.press("f8")
    assert await settle(pilot, lambda: b.has_focus), app.focused
    assert app.query_one("#barkey-b").display is True
    assert app.query_one("#barkey-h").display is True
    assert app.check_action("quit", ()) is not False
    assert b.term.running, "f8 killed the tool"
    await pilot.press("k")                   # an app key, now that it can land
    assert await settle(pilot, lambda: log_text(b) == ""), log_text(b)
    b.term.stop()
    await pilot.pause()
    print("PASS f8 leaves the pane with the tool still running")

    # t is a shell on the device, through su where there is root, with a
    # prompt that names the device, the directory, and which of the two it is.
    await pilot.press("t")
    assert await settle(pilot, lambda: b.term.argv[:1] == ["adb"]), b.term.argv
    assert b.term.argv[:5] == ["adb", "-s", "emulator-5556", "shell", "-t"], b.term.argv
    root_shell = b.term.argv[5]
    # su -p, never su -c: -c runs in a new session, and a shell with no
    # controlling terminal greets you with two warnings about job control.
    assert root_shell == "ENV= PS1='emu64x:$PWD # ' su -p || su", root_shell
    assert b.term.border_title == " adb -s emulator-5556 shell su ", b.term.border_title
    b.term.stop()
    await pilot.pause()
    a.focus()
    await pilot.pause()
    await pilot.press("t")               # 5554 has no root: a plain shell, $ not #
    assert await settle(pilot, lambda: a.term.argv[:1] == ["adb"]), a.term.argv
    assert a.term.argv[:5] == ["adb", "-s", "emulator-5554", "shell", "-t"], a.term.argv
    # No -i either: a pty on stdin makes a shell interactive by itself.
    assert a.term.argv[5] == "ENV= PS1='emu64x:$PWD $ ' exec sh", a.term.argv[5]
    assert "su" not in a.term.argv[5], a.term.argv[5]
    # What is shown for it says what it is, not how the prompt gets set, and
    # it sits off the rule the way the panel title sits off its border.
    assert a.term.border_title == " adb -s emulator-5554 shell ", a.term.border_title
    assert "PS1" not in log_text(a), log_text(a)
    assert "$ adb -s emulator-5554 shell" in log_text(a), log_text(a)
    a.term.stop()
    await pilot.pause()
    b.focus()
    await pilot.pause()
    print("PASS t opens a device shell, su where the device is rooted")

    # scrcpy is an external window: toggling it must track and reap the process.
    app.action_mirror()
    assert await settle(pilot, lambda: b.mirror is not None), log_text(b)
    window = b.mirror
    app.action_mirror()
    assert await settle(pilot, lambda: b.mirror is None), log_text(b)
    # returncode, not wait() or poll(): both of those reap it themselves, which
    # is how closing the window while leaving a zombie behind went unnoticed.
    assert window.returncode is not None, "the scrcpy window was left unreaped"
    print("PASS scrcpy is toggled and its process tracked")

    # A tool stopped from the app must be reaped, not left as a zombie.
    b.term.start(["sh", "-c", "sleep 30"])
    assert await settle(pilot, lambda: b.term.running), "long-running tool never started"
    stopped = b.term.proc
    b.term.stop()
    # returncode, not poll(): poll() reaps the process itself, so a zombie
    # stop() failed to wait on would pass the very check that names it.
    assert stopped.returncode is not None, "stopping a tool left a zombie behind"
    assert not b.has_class("running")
    print("PASS a stopped tool is killed and reaped")

    # frida-client asks for its arguments, remembers them, and runs in the pane.
    app.action_frida_client()
    await confirm(pilot, app, "n")               # spawn it again
    assert await on_screen(pilot, app, moabile.FridaArgsScreen)
    answer = app.screen.query_one("#answer", Input)
    assert answer.value == 'a "unbalanced', "the prompt does not come back prefilled"
    answer.value = "--codeshare ub3rsick/rootbeer-root-detection-bypass -l src/bypass.js"
    await pilot.press("enter")
    assert await settle(pilot, lambda: b.term.argv[:1] == ["frida"], tries=300), b.term.argv
    assert b.term.argv == ["frida", "-D", "emulator-5556", "-f", "com.target.app",
                           "--codeshare", "ub3rsick/rootbeer-root-detection-bypass",
                           "-l", "src/bypass.js"], b.term.argv
    assert b.frida_args.startswith("--codeshare"), "arguments not remembered"
    print("PASS frida-client prompts for arguments and runs them in the pane")

    # An app already up can be attached to rather than spawned again: -p, and
    # whatever it is in the middle of survives — the session it is logged into,
    # the screen it is on. It is also the only way to read what the device log
    # does not carry, since a script on the running process sees it where it is
    # made. Enter and escape keep the spawn, which is what s always did.
    app.action_frida_client()
    await confirm(pilot, app, "y")               # attach to the running one
    assert await on_screen(pilot, app, moabile.FridaArgsScreen)
    # Still a --codeshare line: what the panel remembers is asserted two phases
    # further down, and it is the same field either way it was started.
    app.screen.query_one("#answer", Input).value = "--codeshare user/logger -l hooks.js"
    await pilot.press("enter")
    assert await settle(pilot, lambda: b.term.argv[:1] == ["frida"], tries=300), b.term.argv
    assert b.term.argv == ["frida", "-D", "emulator-5556", "-p", "4242",
                           "--codeshare", "user/logger", "-l", "hooks.js"], b.term.argv
    assert "com.target.app" in b.term.label and "4242" in b.term.label, b.term.label
    b.term.stop()
    await pilot.pause()
    print("PASS s attaches to an app that is already running, or spawns it again")


async def phase_scripts(app, pilot) -> None:
    """picking -l scripts off the disk and --codeshare slugs off the site."""
    _, b = app.panels
    b.focus()
    await pilot.pause()

    scripts = TMP / "scripts"
    (scripts / "sub").mkdir(parents=True, exist_ok=True)
    (scripts / "hook.js").write_text("// hook")
    (scripts / "notes.txt").write_text("not a script")
    (scripts / "sub" / "deep.js").write_text("// deep")
    b.script_dir = str(scripts)

    app.action_frida_client()
    await confirm(pilot, app, "n")               # spawn it again
    assert await on_screen(pilot, app, moabile.FridaArgsScreen)
    prompt = app.screen
    prompt.query_one("#answer", Input).value = ""

    await pilot.press("ctrl+o")
    assert await on_screen(pilot, app, moabile.ScriptScreen)
    picker = app.screen
    entries = picker.side.query_one(ListView)
    # Directories first, .js only: notes.txt has no business in this list.
    assert await settle(pilot, lambda: [n.value for n in entries._nodes] == ["sub/", "hook.js"]), \
        [n.value for n in entries._nodes]
    select(entries, "sub/")
    assert await settle(pilot, lambda: picker.side.path == str(scripts / "sub"))
    await pilot.press("backspace")
    assert await settle(pilot, lambda: picker.side.path == str(scripts))
    select(entries, "hook.js")
    assert await on_screen(pilot, app, moabile.FridaArgsScreen)
    assert prompt.query_one("#answer", Input).value == f"-l {scripts}/hook.js", \
        prompt.query_one("#answer", Input).value
    print("PASS -l scripts are picked off a local directory listing")

    await pilot.press("ctrl+g")
    assert await on_screen(pilot, app, moabile.CodeshareScreen)
    share = app.screen
    hits = share.query_one("#hits", ListView)
    assert await settle(pilot, lambda: len(hits) == 3), [n.value for n in hits._nodes]
    assert "ub3rsick/rootbeer-root-detection-bypass" in [n.value for n in hits._nodes]
    assert share.pages == 4, share.pages          # from the site's own pager
    await pilot.press("ctrl+n")
    assert await settle(pilot, lambda: share.page == 2)
    assert "page=2" in (TMP / "curl-log").read_text(), "the next page was never fetched"
    await pilot.press("ctrl+b")
    assert await settle(pilot, lambda: share.page == 1)
    print("PASS codeshare browse pages through the site")

    needle = share.query_one("#needle", Input)
    needle.focus()
    needle.value = "rootbeer"
    await pilot.press("enter")
    assert await settle(pilot, lambda: share.needle == "rootbeer"
                        and len(hits) == moabile.CODESHARE_PAGE), (share.needle, len(hits))
    assert share.pages == 2, share.pages          # 15 hits cut into pages of 10
    fetched = (TMP / "curl-log").read_text().count("query=rootbeer")
    await pilot.press("ctrl+n")
    assert await settle(pilot, lambda: share.page == 2
                        and len(hits) == 15 - moabile.CODESHARE_PAGE), len(hits)
    assert (TMP / "curl-log").read_text().count("query=rootbeer") == fetched, \
        "search paged by downloading everything again"
    select(hits, "rootbeer/hit-13")
    assert await on_screen(pilot, app, moabile.FridaArgsScreen)
    assert prompt.query_one("#answer", Input).value.endswith("--codeshare rootbeer/hit-13"), \
        prompt.query_one("#answer", Input).value
    print("PASS codeshare search pages locally and returns a slug")

    # No hits is an answer, not a failure: the page parses to nothing and the
    # list has to say so instead of reporting the site as unreachable.
    (TMP / "nohits").touch()
    await pilot.press("ctrl+g")
    assert await on_screen(pilot, app, moabile.CodeshareScreen)
    empty = app.screen
    rows, needle = empty.query_one("#hits", ListView), empty.query_one("#needle", Input)
    needle.focus()
    needle.value = "zzqqxx7"
    await pilot.press("enter")
    assert await settle(pilot, lambda: empty.needle == "zzqqxx7" and empty.found == [])
    assert len(rows) == 1 and rows._nodes[0].value == "", [n.value for n in rows._nodes]
    assert "unreachable" not in str(empty.query_one("#where").render()), \
        "an empty search read as an error"
    assert empty.pages == 1, empty.pages
    await pilot.press("escape")
    (TMP / "nohits").unlink()
    assert await on_screen(pilot, app, moabile.FridaArgsScreen)
    print("PASS a search with no hits shows an empty list, not an error")

    # A dead network has to say so in the panel, not hang or take the app down.
    (TMP / "netdown").touch()
    await pilot.press("ctrl+g")
    assert await on_screen(pilot, app, moabile.CodeshareScreen)
    down = app.screen
    assert await settle(pilot, lambda: "unreachable" in str(down.query_one("#where").render())), \
        str(down.query_one("#where").render())
    await pilot.press("escape")
    (TMP / "netdown").unlink()
    assert await on_screen(pilot, app, moabile.FridaArgsScreen)
    print("PASS a codeshare fetch that fails is reported, not swallowed")

    await pilot.press("escape")
    assert await settle(pilot, lambda: not isinstance(app.screen, moabile.FridaArgsScreen))
    assert b.term.argv[:1] != ["frida"] or not b.term.running, "cancelling still started frida"
    assert b.script_dir == str(scripts), b.script_dir
    print("PASS the script directory is kept per device, for as long as the run lasts")


async def phase_apk(app, pilot) -> None:
    """installing an apk off the host, and saving one back onto it."""
    _, b = app.panels
    b.package = "com.target.app"
    b.focus()
    await pilot.pause()

    apks = TMP / "apks"
    (apks / "sub").mkdir(parents=True, exist_ok=True)
    (apks / "app.apk").write_text("PK")
    (apks / "notes.txt").write_text("not an apk")
    b.local_dir = str(apks)

    # A refused install exits 0 and says "Failure": that has to read as one.
    (TMP / "badapk").touch()
    app.action_install()
    assert await on_screen(pilot, app, moabile.ScriptScreen)
    entries = app.screen.side.query_one(ListView)
    # Directories first, .apk only: notes.txt has no business in this list.
    assert await settle(pilot, lambda: [n.value for n in entries._nodes] == ["sub/", "app.apk"]), \
        [n.value for n in entries._nodes]
    select(entries, "app.apk")
    await confirm(pilot, app)
    assert await settle(pilot, lambda: "INSTALL_FAILED_INVALID_APK" in log_text(b)), log_text(b)
    assert "com.fresh.app" not in b.packages, "a failed install still refreshed the list"
    (TMP / "badapk").unlink()
    (TMP / "resigned").touch()
    rc, out = await b.install("/tmp/repackaged.apk")
    assert rc != 0 and "uninstall com.target.app" in out, out
    assert "removes the app's data too" in out, out
    (TMP / "resigned").unlink()
    print("PASS a signature that does not match names the one thing that fixes it")

    app.action_install()
    assert await on_screen(pilot, app, moabile.ScriptScreen)
    select(app.screen.side.query_one(ListView), "app.apk")
    await confirm(pilot, app)
    assert await settle(pilot, lambda: "Success" in log_text(b)), log_text(b)
    assert f"install -r {apks}/app.apk" in (TMP / "adb-log").read_text()
    # Installed means installable: the sidebar list has to know about it.
    assert await settle(pilot, lambda: "com.fresh.app" in b.packages), b.packages

    # Cancelling installs nothing.
    before = (TMP / "adb-log").read_text().count("install -r")
    app.action_install()
    assert await on_screen(pilot, app, moabile.ScriptScreen)
    await pilot.press("escape")
    await pilot.pause()
    assert (TMP / "adb-log").read_text().count("install -r") == before, "escape still installed"

    # Saving an apk: base and split, named after the package, into a directory.
    app.action_save_app()
    assert await on_screen(pilot, app, moabile.ScriptScreen)
    picker = app.screen
    assert picker.pick_dir
    # A file is not a destination — enter on one must not answer the picker.
    select(picker.side.query_one(ListView), "app.apk")
    await pilot.pause()
    assert app.screen is picker, "a file was taken as the destination"
    await pilot.press("s")
    assert await settle(pilot, lambda: (apks / "com.target.app-base.apk").exists()), \
        sorted(pt.name for pt in apks.iterdir())
    assert (apks / "com.target.app-split_config.arm64.apk").exists(), \
        sorted(pt.name for pt in apks.iterdir())
    assert b.local_dir == str(apks), b.local_dir      # the browser reopens where it was

    # If the file already exists, saving asks for overwrite confirmation
    app.action_save_app()
    assert await on_screen(pilot, app, moabile.ScriptScreen)
    await pilot.press("s")
    assert await on_screen(pilot, app, moabile.ConfirmScreen)
    await pilot.press("n")
    assert await settle(pilot, lambda: "export cancelled" in log_text(b)), log_text(b)
    print("PASS apks are installed from and saved to a host directory")


async def phase_streams(app, pilot) -> None:
    """log streams and the text that goes through them."""
    a, b = app.panels

    b.start_stream("huge", "python3", "-c", "print('y' * 200000); print('after the long line')")
    # The line after it, and nothing about the line itself: 200k characters
    # wrap into thousands of rows, more than the log keeps, so how much of it
    # is still there is the log's business — the same reasoning the flood
    # below is checked by. What is being tested is that a line larger than the
    # reader's own 64 KiB chunk did not take the stream down with it.
    assert await settle(pilot, lambda: "after the long line" in log_text(b), tries=200), \
        "stream died"
    print("PASS a stream line larger than the read buffer is handled")

    # A flood, and a line with no newline in sight. logcat outruns the display,
    # so the reader coalesces and caps: neither may take the app down, and the
    # end of the flood has to arrive.
    b.start_stream("flood", "python3", "-c",
                   "import sys\n"
                   "for i in range(4000): print(f'line {i}')\n"
                   "sys.stdout.write('z' * 1_500_000)\n"
                   "sys.stdout.flush()\n"
                   "print()\nprint('end of the flood')")
    # That the end arrives is the whole property: the reader coalesced four
    # thousand lines and cut a line with no end to it loose, and the panel is
    # still reading. What scrolled off the log on the way is the log's business.
    assert await settle(pilot, lambda: "end of the flood" in log_text(b), tries=400), "the flood"
    print("PASS a flooding stream is capped rather than growing without end")

    # Any logcat line containing "[/]" used to be parsed as Rich markup and
    # took the whole app down with a MarkupError from inside the worker.
    # On an empty log, and with the two streams above stopped first: the
    # flood's last line is a megabyte and a half still on its way through the
    # reader, and it lands in the middle of whatever is checked next unless it
    # is waited out — the clear alone raced it.
    b.stop_stream("huge")
    b.stop_stream("flood")
    await pilot.pause(0.5)                       # their last flush lands
    b.query_one(RichLog).clear()
    b.write("literal [/] from a device")
    b.start_stream("probe", "sh", "-c", r"printf 'D/App( 12): state=[/]\nE/Auth: token=[bold]\n'")
    assert await settle(pilot, lambda: "state=[/]" in log_text(b)), log_text(b)
    assert "token=[bold]" in log_text(b), log_text(b)[-200:]
    assert "literal [/] from a device" in log_text(b), log_text(b)[-200:]
    print("PASS raw output with markup characters is logged, not parsed")

    # Asked for twice before the first has spawned. The spawn is a worker, so
    # the second used to start a stream of its own and overwrite the handle on
    # the first — which then ran on with nothing left to stop it.
    twice = TMP / "twice"
    b.start_stream("twice", "sh", "-c", f"echo x >> {twice}; sleep 30")
    b.start_stream("twice", "sh", "-c", f"echo x >> {twice}; sleep 30")
    assert await settle(pilot, lambda: "twice" in b.streams), b.streams
    await pilot.pause(0.3)
    assert twice.read_text() == "x\n", twice.read_text()
    assert b.stop_stream("twice"), "the stream that did start cannot be stopped"
    assert not b.stop_stream("twice"), "a second stream was left running"
    print("PASS a stream asked for twice before it is up starts once")

    b.focus()
    await pilot.pause()
    await pilot.press("k")
    assert log_text(b) == "", log_text(b)
    assert log_text(a) != "", "k emptied the wrong panel"
    print("PASS k clears the active panel's log")

    # / filters log stream by keyword and shows badge in stats
    b.write("line one hello")
    b.write("line two error occurred")
    await pilot.press("slash")
    assert await on_screen(pilot, app, moabile.AskScreen, tries=200), app.screen
    app.screen.query_one("#answer", Input).value = "error"
    await pilot.press("enter")
    assert b.log_filter == "error"
    assert "/error" in _stats(b), _stats(b)
    # Clear filter with / and empty input
    await pilot.press("slash")
    assert await on_screen(pilot, app, moabile.AskScreen, tries=200), app.screen
    app.screen.query_one("#answer", Input).value = ""
    await pilot.press("enter")
    assert b.log_filter == ""
    assert "/error" not in _stats(b), _stats(b)
    # Focusing sidebar package filter disables / filter_logs hotkey
    pkg_input = app.query_one("#filter", Input)
    pkg_input.focus()
    await pilot.pause()
    assert app.check_action("filter_logs", ()) is False
    assert app.check_action("quit", ()) is False
    assert app.query_one("#barkey-b").display is False
    assert app.query_one("#barkey-h").display is False
    b.focus()
    await pilot.pause()
    assert app.query_one("#barkey-b").display is True
    assert app.query_one("#barkey-h").display is True
    assert app.check_action("quit", ()) is not False
    print("PASS / filters log stream by keyword and shows badge in stats")

    # c opens log history in selectable read-only TextViewer modal
    await pilot.press("c")
    assert await on_screen(pilot, app, moabile.TextViewerScreen, tries=200), app.screen
    area = app.screen.query_one(moabile.TextArea)
    assert area.read_only is True
    assert "line two error occurred" in area.text, area.text
    # c in TextViewerScreen copies to clipboard
    await pilot.press("c")
    assert "line two error occurred" in app._clipboard
    # ctrl+a selects all text
    await pilot.press("ctrl+a")
    assert area.selected_text == area.text
    await pilot.press("escape")
    assert await settle(pilot, lambda: not isinstance(app.screen, moabile.TextViewerScreen)), app.screen
    # q also closes TextViewerScreen
    await pilot.press("c")
    assert await on_screen(pilot, app, moabile.TextViewerScreen, tries=200), app.screen
    await pilot.press("q")
    assert await settle(pilot, lambda: not isinstance(app.screen, moabile.TextViewerScreen)), app.screen
    print("PASS c opens log history in selectable read-only TextViewer modal and copies to clipboard")

    # logcat is asked for whole or filtered every time it starts: a filter is
    # invisible once the stream is scrolling.
    await pilot.press("l")
    await confirm(pilot, app, "n")                 # everything on the device
    assert await settle(pilot, lambda: "logcat" in b.streams), b.streams
    started = log_text(b).rsplit("$ adb", 1)[-1]
    assert "--pid" not in started, started
    # The stats line says what is running against the device, logcat included.
    assert await settle(pilot, lambda: "logcat ●" in _stats(b)), _stats(b)
    await pilot.press("l")
    assert await settle(pilot, lambda: "logcat" not in b.streams), b.streams
    await pilot.press("l")
    await confirm(pilot, app, "y")                 # only com.target.app, pid 4242
    assert await settle(pilot, lambda: "--pid=4242" in log_text(b)), log_text(b)
    # And says so, with what a pid costs: the app restarting gets a new one.
    assert "filtering on pid 4242" in log_text(b), log_text(b)
    assert "l twice" in log_text(b), log_text(b)
    await pilot.press("l")
    assert await settle(pilot, lambda: "logcat" not in b.streams), b.streams
    assert await settle(pilot, lambda: "logcat ○" in _stats(b)), _stats(b)
    # One line for the end of a stream, not one from the killer and one from
    # the stream itself.
    assert await settle(pilot, lambda: "logcat ended" in log_text(b)), log_text(b)
    assert "logcat stopped" not in log_text(b), log_text(b)
    print("PASS logcat runs whole or filtered to the package, as asked")

    # The filter is the pid, so an app that is not up has none: the question is
    # not asked at all — it used to offer a narrowing it could not apply and
    # hand back the whole device anyway — and the stream is everything, with
    # one line saying why. An app that is not on the device is a different
    # thing to know from one that is simply not up.
    (TMP / "running-emulator-5556").unlink(missing_ok=True)
    await pilot.press("l")
    assert await settle(pilot, lambda: "logcat" in b.streams, tries=200), b.streams
    assert not isinstance(app.screen, moabile.ConfirmScreen), "asked with no pid to answer"
    assert "--pid" not in log_text(b).rsplit("$ adb", 1)[-1], log_text(b)
    assert "no pid for com.target.app" in log_text(b), log_text(b)
    await pilot.press("l")
    assert await settle(pilot, lambda: "logcat" not in b.streams), b.streams

    was_package, b.package = b.package, "com.not.installed"
    await pilot.press("l")
    assert await settle(pilot, lambda: "logcat" in b.streams, tries=200), b.streams
    assert "is not installed on this device" in log_text(b), log_text(b)
    await pilot.press("l")
    assert await settle(pilot, lambda: "logcat" not in b.streams), b.streams
    b.package = was_package
    (TMP / "running-emulator-5556").touch()
    print("PASS with no pid there is no filter to offer, and the log says why")


async def phase_files(app, pilot) -> None:
    """deselecting the app, both filesystems, and the system dump."""
    _, b = app.panels

    b.focus()
    await pilot.pause()
    select(app.query_one("#packages", ListView), "")
    assert await settle(pilot, lambda: b.package is None), b.package
    assert "no app selected" in log_text(b), log_text(b)
    select(app.query_one("#packages", ListView), "com.target.app")
    assert await settle(pilot, lambda: b.package == "com.target.app")
    # The title bar says which panel and package the keys are about.
    assert app.sub_title == "emulator-5556 · com.target.app", app.sub_title
    print("PASS the package can be deselected again")

    await pilot.press("i")
    assert await settle(pilot, lambda: "selinux" in log_text(b)), log_text(b)
    assert "Enforcing" in log_text(b) and "yes — su works" in log_text(b), log_text(b)
    # The same row the ios dump has: whether frida-server is up belongs in a
    # summary of what the device is, and it is the pid, not the table it came
    # out of.
    assert re.search(r"frida\s+(pid \d+|not running)", log_text(b)), log_text(b)
    # And the timezone, which the ios dump gets from lockdownd for nothing: a
    # summary that carries it on one family and not the other is two summaries.
    assert "Europe/Rome" in log_text(b), log_text(b)
    print("PASS i dumps a system summary into the panel")

    await pilot.press("d")
    assert await on_screen(pilot, app, moabile.FilesScreen)
    files = app.screen
    host, device = files.host, files.device
    device_entries = device.query_one(ListView)
    host_entries = host.query_one(ListView)
    assert await settle(pilot, lambda: len(device_entries) == 3), len(device_entries)
    # Directories first, however the device orders them.
    assert [n.value for n in device_entries._nodes] == ["Android/", "Download/", "note.txt"]
    # Two filesystems, side by side: the machine adb runs on and the device.
    assert "host" in str(host.query_one(Static).render()), str(host.query_one(Static).render())
    assert "android" in str(device.query_one(Static).render()) and "emulator-5556" \
        in str(device.query_one(Static).render()), str(device.query_one(Static).render())
    assert await settle(pilot, lambda: device_entries.has_focus), \
        "the device side did not take focus"

    # Typing a path in either column goes there.
    host.query_one(Input).value = str(TMP)
    host.query_one(Input).focus()
    await pilot.press("enter")
    assert await settle(pilot, lambda: host.path == str(TMP) and host_entries.has_focus), host.path
    assert await settle(pilot, lambda: any(n.value == "bin/" for n in host_entries._nodes)), \
        [n.value for n in host_entries._nodes]
    # Both directions are spelled out, with the two directories in them.
    where = str(files.query_one("#where").render())
    assert f"pull android /sdcard → host {TMP}" in where, where
    assert f"push host {TMP} → android /sdcard" in where, where
    print("PASS the browser shows the host and the device side by side")

    select(device_entries, "Download/")
    assert await settle(pilot, lambda: device.path == "/sdcard/Download")
    device_entries.focus()
    await pilot.press("backspace")
    assert await settle(pilot, lambda: device.path == "/sdcard"), device.path
    # backspace moves whichever side has focus, and no other.
    host_entries.focus()
    await pilot.press("backspace")
    assert await settle(pilot, lambda: host.path == str(TMP.parent) and device.path == "/sdcard"), \
        (host.path, device.path)
    host.go(str(TMP))
    assert await settle(pilot, lambda: host.path == str(TMP))

    # In a directory with only one item, it must still be highlighted with the -highlight class
    single_dir = TMP / "single_folder"
    single_dir.mkdir(exist_ok=True)
    (single_dir / "lone_file.txt").write_text("hello")
    host.go(str(single_dir))
    assert await settle(pilot, lambda: host.path == str(single_dir) and len(host_entries._nodes) == 1)
    assert host_entries.children[0].has_class("-highlight"), "single item in directory did not receive -highlight class"
    assert host_entries.highlighted_child is not None
    assert host_entries.highlighted_child.value == "lone_file.txt"
    host.go(str(TMP))
    assert await settle(pilot, lambda: host.path == str(TMP) and any(n.value == "bin/" for n in host_entries._nodes))
    shutil.rmtree(single_dir, ignore_errors=True)
    print("PASS a directory with a single item highlights its lone element")

    # Enter on a device file pulls it to wherever the host side is standing.
    # Refused: the confirmation is not a formality, "n" has to stop it.
    select(device_entries, "note.txt")
    await confirm(pilot, app, "n")
    await pilot.pause(0.2)
    assert not (TMP / "note.txt").exists(), "a refused pull ran anyway"
    select(device_entries, "note.txt")
    await confirm(pilot, app)
    assert await settle(pilot, lambda: (TMP / "note.txt").exists()), log_text(b)
    assert (TMP / "note.txt").read_text().strip() == "pulled-from-/sdcard/note.txt"

    # Pulling a file that already exists on the host asks for overwrite confirmation
    select(device_entries, "note.txt")
    await confirm(pilot, app, "n")
    assert await settle(pilot, lambda: "pull cancelled" in log_text(b)), log_text(b)
    print("PASS enter on a device file pulls it to the host directory")

    # l pulls whatever the cursor is on, a directory included.
    device_entries.index = [n.value for n in device_entries._nodes].index("Download/")
    await pilot.press("l")
    await confirm(pilot, app)
    assert await settle(pilot, lambda: (TMP / "Download").exists()), log_text(b)
    print("PASS l pulls the highlighted directory, not just a file")

    # adb pull cannot read /data/data; on a rooted device it falls back to su.
    files.transfer("pull", "/data/data/com.target.app/prefs.xml")
    await confirm(pilot, app)
    assert await settle(pilot, lambda: (TMP / "prefs.xml").exists()), log_text(b)
    assert (TMP / "prefs.xml").read_text().strip() == "root-only-bytes"
    assert "via su" in log_text(b), log_text(b)

    # p pushes what the host cursor is on into the device directory, and the
    # device side reloads so the file that just landed is visible.
    device.go("/data/data/com.target.app")
    assert await settle(pilot, lambda: device.path == "/data/data/com.target.app")
    host_entries.index = [n.value for n in host_entries._nodes].index("note.txt")
    host_entries.focus()
    (TMP / "edits").write_text("")
    await pilot.press("p")
    await confirm(pilot, app)
    assert await settle(pilot, lambda: "moved as root" in log_text(b)), log_text(b)
    log = (TMP / "adb-log").read_text().splitlines()
    pushed = [ln for ln in log if ln.startswith("push ")]
    # adb push is no more root than adb pull is, and the app's own directory is
    # where a is one keypress away: refused where it was aimed, staged where
    # adb can write, moved into place through su. The same three steps the ios
    # side takes through sudo, which is the point — the key does one thing.
    assert pushed[-2] == f"push {TMP}/note.txt /data/data/com.target.app", pushed[-2]
    assert pushed[-1] == f"push {TMP}/note.txt /data/local/tmp/note.txt", pushed[-1]
    assert "su -c 'mv /data/local/tmp/note.txt /data/data/com.target.app'" \
        in (TMP / "edits").read_text(), (TMP / "edits").read_text()
    # The side that received it lists itself again, so the file is on screen.
    # Not log[-1]: the three-second status poll lands between often enough.
    after = log[max(i for i, line in enumerate(log) if line.startswith("push ")):]
    assert any("ls -pA /data/data/com.target.app" in line for line in after), after
    print("PASS p pushes into the device directory")

    # Renaming and deleting, on whichever side has focus. On the host they are
    # real files, so this is checked on disk, not in the log.
    (TMP / "scratch.txt").write_text("scratch")
    host.reload()
    assert await settle(pilot, lambda: any(n.value == "scratch.txt"
                                          for n in host_entries._nodes)), \
        [n.value for n in host_entries._nodes]
    host_entries.index = [n.value for n in host_entries._nodes].index("scratch.txt")
    host_entries.focus()
    await pilot.press("n")
    assert await on_screen(pilot, app, moabile.AskScreen), app.screen
    app.screen.query_one("#answer", Input).value = "renamed.txt"
    await pilot.press("enter")
    assert await settle(pilot, lambda: (TMP / "renamed.txt").exists()), log_text(b)
    assert not (TMP / "scratch.txt").exists(), "the old name is still there"

    # Renaming to an existing name asks for overwrite confirmation
    (TMP / "dup.txt").write_text("dup")
    host.reload()
    assert await settle(pilot, lambda: any(n.value == "dup.txt" for n in host_entries._nodes))
    host_entries.index = [n.value for n in host_entries._nodes].index("dup.txt")
    host_entries.focus()
    await pilot.press("n")
    assert await on_screen(pilot, app, moabile.AskScreen), app.screen
    app.screen.query_one("#answer", Input).value = "renamed.txt"
    await pilot.press("enter")
    await confirm(pilot, app, "n")
    assert await settle(pilot, lambda: "rename cancelled" in log_text(b)), log_text(b)
    (TMP / "dup.txt").unlink(missing_ok=True)
    host.reload()
    assert await settle(pilot, lambda: not any(n.value == "dup.txt" for n in host_entries._nodes))

    host_entries.index = [n.value for n in host_entries._nodes].index("renamed.txt")
    await pilot.press("d")
    await confirm(pilot, app, "n")               # refused: it stays
    await pilot.pause(0.2)
    assert (TMP / "renamed.txt").exists(), "a refused delete removed it anyway"
    await pilot.press("d")
    await confirm(pilot, app)
    assert await settle(pilot, lambda: not (TMP / "renamed.txt").exists()), log_text(b)
    print("PASS n renames and d deletes on the host side")

    # On the device the same two keys go out as shell commands, through su.
    device_entries.focus()
    device_entries.index = [n.value for n in device_entries._nodes].index("note.txt")
    await pilot.press("n")
    assert await on_screen(pilot, app, moabile.AskScreen), app.screen
    app.screen.query_one("#answer", Input).value = "note.bak"
    await pilot.press("enter")
    assert await settle(pilot, lambda: (TMP / "edits").exists() and
                        "mv" in (TMP / "edits").read_text(), tries=200), "no mv reached the device"
    edits = (TMP / "edits").read_text()
    assert "su -c 'mv /data/data/com.target.app/note.txt" in edits, edits
    # Focus comes back where it was, or the next key does nothing at all.
    assert await settle(pilot, lambda: device_entries.has_focus), app.screen.focused
    assert "/data/data/com.target.app/note.bak" in edits, edits

    # Renaming to an existing name on device asks for overwrite confirmation
    (TMP / "edits").write_text("")
    device_entries.focus()
    device_entries.index = [n.value for n in device_entries._nodes].index("note.txt")
    await pilot.press("n")
    assert await on_screen(pilot, app, moabile.AskScreen), app.screen
    app.screen.query_one("#answer", Input).value = "existing.txt"
    await pilot.press("enter")
    assert await on_screen(pilot, app, moabile.ConfirmScreen)
    await pilot.press("n")
    assert await settle(pilot, lambda: "rename cancelled" in log_text(b)), log_text(b)

    device_entries.index = [n.value for n in device_entries._nodes].index("note.txt")
    # A rename is a name and never a path: the host side is refused by Path
    # itself, and the device side would have moved the file out of the
    # directory the question named.
    (TMP / "edits").write_text("")
    await pilot.press("n")
    assert await on_screen(pilot, app, moabile.AskScreen), app.screen
    app.screen.query_one("#answer", Input).value = "../note.bak"
    await pilot.press("enter")
    await pilot.pause(0.3)
    assert "mv" not in (TMP / "edits").read_text(), (TMP / "edits").read_text()
    print("PASS a rename with a path in it is refused, on both sides")

    # Only what this delete sends. The file collects every edit anything makes
    # to the device, and p — taking frida-server off it — uses rm -rf for a
    # directory quite legitimately, so the check below has to be about this
    # keypress rather than about the whole run.
    (TMP / "edits").write_text("")
    await pilot.press("d")
    await confirm(pilot, app)
    assert await settle(pilot, lambda: "rm -f" in (TMP / "edits").read_text(), tries=200), \
        (TMP / "edits").read_text()
    # Quoted as one word: adb joins what it is given and the shell on the
    # device parses it again, so `rm -f 'my file'` unquoted reached su as three
    # arguments — a delete of whatever else was named.
    assert "su -c 'rm -f /data/data/com.target.app/note.txt'" in (TMP / "edits").read_text()
    assert "rm -rf" not in (TMP / "edits").read_text(), "recursive delete is back"
    # A name with a space in it is where that mattered: shlex.split does to the
    # line what the device's shell does to it, and su has to come out of that
    # holding one argument — the whole script — not three.
    (TMP / "edits").write_text("")
    await b.run(f"rm -f {shlex.quote('/sdcard/my file.txt')}")
    line = (TMP / "edits").read_text().strip()
    assert shlex.split(line)[1:] == ["su", "-c", "rm -f '/sdcard/my file.txt'"], line
    print("PASS n and d reach the device as mv and rm, through su, whole")

    # MASTG-TECH-0008: the internal data directory, which is where the
    # databases and the shared_prefs are and which sits behind root.
    files.device.go("/sdcard")
    assert await settle(pilot, lambda: files.device.path == "/sdcard"), files.device.path
    await pilot.press("a")
    assert await settle(pilot, lambda: files.device.path == "/data/data/com.target.app",
                        tries=200), files.device.path
    assert "ls -pA /data/data/com.target.app" in (TMP / "adb-log").read_text(), \
        "the data directory was never listed"
    print("PASS a jumps the device side to the app's own data directory")

    # And back out of it, which is otherwise four levels of backspace: the data
    # directory and everything else worth reaching are deep, and the column has
    # no path to type over that anybody remembers.
    await pilot.press("h")
    assert await settle(pilot, lambda: files.device.path == b.home_dir), files.device.path
    # h is the help key everywhere else, and the modal is what decides that.
    assert isinstance(app.screen, moabile.FilesScreen), "h opened help over the browser"
    print("PASS h takes the device side back to where it opened")
    await pilot.press("a")                       # and back, for what follows
    assert await settle(pilot, lambda: files.device.path == "/data/data/com.target.app",
                        tries=200), files.device.path

    # A directory is not something these two keys touch: no prompt, no adb.
    edits_before = (TMP / "edits").read_text()
    device_entries.index = [n.value for n in device_entries._nodes].index("Download/")
    for key in ("d", "n"):
        await pilot.press(key)
        await pilot.pause(0.2)
        assert isinstance(app.screen, moabile.FilesScreen), f"{key} opened a screen on a directory"
    assert (TMP / "edits").read_text() == edits_before, (TMP / "edits").read_text()
    # Same on the host: the directory is still there afterwards.
    (TMP / "keepme").mkdir(exist_ok=True)
    host.reload()
    assert await settle(pilot, lambda: any(n.value == "keepme/" for n in host_entries._nodes)), \
        [n.value for n in host_entries._nodes]
    host_entries.focus()
    host_entries.index = [n.value for n in host_entries._nodes].index("keepme/")
    await pilot.press("d")
    await pilot.pause(0.2)
    assert (TMP / "keepme").is_dir(), "a directory was deleted"
    assert isinstance(app.screen, moabile.FilesScreen), "d prompted for a directory"
    device_entries.focus()
    print("PASS directories cannot be renamed or deleted, only files")

    await pilot.press("escape")
    assert await settle(pilot, lambda: not isinstance(app.screen, moabile.FilesScreen))
    assert (b.remote_dir, b.local_dir) == ("/data/data/com.target.app", str(TMP)), \
        (b.remote_dir, b.local_dir)
    print("PASS both paths are remembered")


async def phase_resilience(app, pilot) -> None:
    """staying responsive while the device is slow."""
    _, b = app.panels

    b.focus()
    await pilot.pause()
    (TMP / "slow").touch()
    try:
        # The timer keeps firing while adb is slow, and the overlapping polls
        # used to pile up until the interface stopped responding altogether.
        app._ticking = True
        before = (TMP / "adb-log").read_text().count("@batt")
        app.tick()
        await pilot.pause(0.3)
        assert (TMP / "adb-log").read_text().count("@batt") == before, \
            "a status poll ran while one was already in flight"
        app._ticking = False
        print("PASS overlapping status polls are skipped, not queued")

        # A poll waiting on a slow device must not stall the interface: keys
        # that touch nothing but the screen still have to answer at once.
        app.tick()
        await pilot.pause(0.05)
        began = time.monotonic()
        await pilot.press("k")
        assert log_text(b) == "", "k did not reach the panel while adb was busy"
        assert time.monotonic() - began < 2, "the interface waited for adb"
        print("PASS a slow device call does not block the interface")
    finally:
        (TMP / "slow").unlink()
        app._ticking = False

    # frida-server stopped is not a device that stopped answering. The poll is
    # one batch, a shell exits with the status of the last command in it, and
    # that command is pgrep — or pidof, with an app selected — each of which
    # exits 1 when it matches nothing. Reading the poll's own readings, and not
    # that status, is what tells the two apart.
    was = [f for f in (TMP / "frida-up", TMP / f"running-{b.serial}") if f.exists()]
    for f in was:                                # as if f had just stopped it
        f.unlink()
    saved, b.package = b.package, ""
    try:
        now = await b.stats()                    # the batch ends in pgrep
        assert (now["batt"], now["frida"]) == ("87", ""), now
        assert "stats unavailable" not in log_text(b), log_text(b)
        b.package = saved
        now = await b.stats()                    # and in pidof, with an app
        assert now["batt"] == "87", now
        assert "stats unavailable" not in log_text(b), log_text(b)
    finally:
        b.package = saved
        for f in was:
            f.touch()
    print("PASS a stopped frida-server is not reported as a device gone quiet")

    # A device that stops answering: three ? and no reason is the hardest thing
    # in here to tell apart, so each of the three reads says why — once, the
    # way the ios side has always done it.
    (TMP / "nostats").touch()
    now = await b.stats()
    assert (now["batt"], now["load"], now["mem"]) == ("?", "?", "?"), now
    assert log_text(b).count("stats unavailable") == 1, log_text(b)
    await b.stats()
    assert log_text(b).count("stats unavailable") == 1, "said twice"
    (TMP / "nostats").unlink()
    now = await b.stats()
    assert now["batt"] == "87", now
    (TMP / "nostats").touch()                    # and again after it has worked
    await b.stats()
    assert log_text(b).count("stats unavailable") == 2, log_text(b)
    (TMP / "nostats").unlink()

    (TMP / "noprops").touch()
    await b.describe()
    assert not b.props, b.props
    assert "stopped answering adb" in log_text(b), log_text(b)
    (TMP / "noprops").unlink()
    await b.describe()                           # answering again
    assert b.props.get("ro.product.model"), b.props

    (TMP / "nopkgs").touch()
    await b.load_packages()
    assert b.packages == [], b.packages
    assert "no apps listed" in log_text(b), log_text(b)
    (TMP / "nopkgs").unlink()
    await b.load_packages()
    assert "com.target.app" in b.packages, b.packages
    print("PASS a device that stops answering says so, once, on every reading")

    # What the device calls an app becomes a path on this machine the moment e
    # saves the apk under it, so an identifier that is a path is not one this
    # takes. Nor is an entry in the file browser: enter, d and n would work on
    # something the column never showed.
    (TMP / "hostile-pkg").touch()
    await b.load_packages()
    assert all(moabile.is_package(name) for name in b.packages), b.packages
    assert "com.target.app" in b.packages, b.packages
    (TMP / "hostile-pkg").unlink()
    (TMP / "hostile-ls").touch()
    try:
        b.focus()
        await pilot.pause()
        await pilot.press("d")
        assert await on_screen(pilot, app, moabile.FilesScreen)
        entries = app.screen.device.query_one(ListView)
        assert await settle(pilot, lambda: len(entries) == 3), [n.value for n in entries._nodes]
        assert [n.value for n in entries._nodes] == ["Android/", "Download/", "note.txt"], \
            [n.value for n in entries._nodes]
        await pilot.press("escape")
        assert await settle(pilot, lambda: not isinstance(app.screen, moabile.FilesScreen))
    finally:
        (TMP / "hostile-ls").unlink()
    await b.load_packages()
    print("PASS a path where the device was asked for a name is dropped, not acted on")

    # A notification is parsed as markup by default, and half of what goes into
    # one is device output. A "[/]" in a line off the device was a MarkupError
    # raised inside the toast's own render — and an exception there takes the
    # whole app down, with no panel left to write it to. The same trap the log
    # and every Static.update() in here were already built for. Widget.notify
    # passes its own markup=True down, so the app is where it has to go.
    hostile = "adb: error: failed to copy [/] [bold]"
    try:
        Content.from_markup(hostile)
        raise AssertionError("markup this shape is what used to crash the toast")
    except MarkupError:
        pass
    app.clear_notifications()
    b.fail(hostile)
    await pilot.pause()
    queued = list(app._notifications)
    assert queued, "the failure never reached a notification"
    assert all(note.markup is False for note in queued), queued
    assert any(hostile in note.message for note in queued), queued
    assert hostile in log_text(b), log_text(b)
    app.clear_notifications()
    print("PASS a device line that is not markup cannot crash a notification")


async def phase_frida_server(app, pilot) -> None:
    """installing, starting, reusing and stopping frida-server."""
    _, b = app.panels

    # Nothing about the run is written down: no file to leave behind, and
    # nothing to say afterwards which app on which phone was being poked at.
    assert not list(Path(TMP).glob("*.json")), list(Path(TMP).glob("*.json"))
    assert b.frida_args and "--codeshare" in b.frida_args, b.frida_args
    print("PASS what a panel is pointed at lives in the panel, not on disk")

    # `pgrep -f frida-server` matches the very `sh -c` adb wraps it in, so the
    # status was stuck on "on" whether or not a server was running.
    log = (TMP / "adb-log").read_text()
    assert "[f]rida-server" in log, "the self-matching pgrep pattern is back"
    assert "pgrep -f frida-server" not in log, "unbracketed pattern still issued"
    # And a device that cannot find pgrep at all answers "sh: 1: pgrep: not
    # found" — a digit in a line, which used to be read as frida on pid 1.
    (TMP / "nopgrep").touch()
    now = await b.stats()
    assert now["frida"] == "", now
    (TMP / "nopgrep").unlink()
    print("PASS frida status uses a pattern that cannot match its own shell")

    # Nowhere to cache is a line in the panel, not the app going down: CACHE
    # comes off XDG_CACHE_HOME or HOME, and an OSError raised inside a worker
    # takes every panel's record of the work with it.
    kept_cache, blocked = moabile.CACHE, TMP / "blocked-cache"
    blocked.write_text("a file where the cache directory would go")
    moabile.CACHE = blocked / "moabile"
    try:
        b.prune_cache("16.5.9")              # must not raise
    finally:
        moabile.CACHE = kept_cache
        blocked.unlink()
    print("PASS a cache directory that cannot be made is not a crash")

    cached = moabile.CACHE / "frida-server-16.5.9-android-arm64"
    assert moabile.CACHE == TMP / ".cache" / "moabile", moabile.CACHE
    (TMP / "frida-up").unlink(missing_ok=True)
    cached.unlink(missing_ok=True)
    b.focus()
    await pilot.pause()
    await b.refresh_stats()
    assert "9001" not in _stats(b), _stats(b)

    await pilot.press("f")               # off -> prompt for install
    assert await on_screen(pilot, app, moabile.ConfirmScreen, tries=200), app.screen
    await pilot.press("n")               # cancel
    assert await settle(pilot, lambda: not (TMP / "frida-up").exists(), tries=200), log_text(b)
    assert "is up, pid 9001" not in log_text(b)

    await pilot.press("f")               # off -> prompt for install
    assert await on_screen(pilot, app, moabile.ConfirmScreen, tries=200), app.screen
    await pilot.press("y")               # install client version
    assert await settle(pilot, lambda: "is up, pid 9001" in log_text(b), tries=200), log_text(b)
    install = log_text(b)
    assert str(cached) in install and "/data/local/tmp/frida-server" in install, install
    assert "chmod   755 /data/local/tmp/frida-server" in install, install
    assert "nohup /data/local/tmp/frida-server" in install, install
    assert cached.stat().st_size > moabile.MIN_SERVER_BYTES, cached.stat().st_size
    assert cached.read_bytes().startswith(b"FAKE-FRIDA-SERVER-PAYLOAD"), "not cached"
    await b.refresh_stats()
    assert "frida ● 9001" in _stats(b), _stats(b)
    print("PASS f installs and starts frida-server, naming every path")

    await pilot.press("f")               # on -> stop
    assert await settle(pilot, lambda: "frida-server stopped" in log_text(b),
                        tries=200), log_text(b)
    assert not (TMP / "frida-up").exists(), "server was not killed"
    await b.refresh_stats()
    assert "9001" not in _stats(b), _stats(b)
    print("PASS f is a toggle: pressing it again stops the server")

    # A server already at /data/local/tmp must not be replaced without asking:
    # it can be the same build, or one someone put there on purpose.
    (TMP / "server-there").touch()
    await pilot.press("f")
    assert await on_screen(pilot, app, moabile.ConfirmScreen, tries=200), app.screen
    await pilot.press("n")               # keep what is already there
    assert await settle(pilot, lambda: "already on the device is up, pid 9001" in log_text(b),
                        tries=200), log_text(b)
    pushes = (TMP / "adb-log").read_text().count("push ")
    print("PASS an existing frida-server is started, not overwritten behind your back")

    await pilot.press("f")               # stop it again
    assert await settle(pilot, lambda: not (TMP / "frida-up").exists(), tries=200), log_text(b)
    await pilot.press("f")
    assert await on_screen(pilot, app, moabile.ConfirmScreen, tries=200), app.screen
    await pilot.press("y")               # replace it after all
    assert await settle(pilot, lambda: (TMP / "adb-log").read_text().count("push ") > pushes,
                        tries=200), log_text(b)
    assert await settle(pilot, lambda: "is up, pid 9001" in log_text(b), tries=200), log_text(b)
    assert "purge   /data/local/tmp/frida-server" in log_text(b), log_text(b)
    (TMP / "server-there").unlink()
    await pilot.press("f")               # leave it stopped for what follows
    assert await settle(pilot, lambda: not (TMP / "frida-up").exists(), tries=200), log_text(b)
    print("PASS y replaces the server on the device, n starts what is there")

    # c on ConfirmScreen prompts for a custom version and installs it
    (TMP / "server-there").touch()
    await pilot.press("f")
    assert await on_screen(pilot, app, moabile.ConfirmScreen, tries=200), app.screen
    await pilot.press("c")
    assert await on_screen(pilot, app, moabile.AskScreen, tries=200), app.screen
    app.screen.query_one("#answer", Input).value = "16.5.9"
    await pilot.press("enter")
    assert await settle(pilot, lambda: "frida-server 16.5.9 (arm64) is up" in log_text(b), tries=200), log_text(b)
    (TMP / "server-there").unlink(missing_ok=True)
    await pilot.press("f")               # stop it
    assert await settle(pilot, lambda: not (TMP / "frida-up").exists(), tries=200), log_text(b)
    print("PASS c allows installing a specific custom frida-server version")

    # A truncated download is an error page or a cut connection, never a
    # server; pushing it would fail obscurely on the device instead.
    cached.unlink(missing_ok=True)
    (TMP / "tiny").touch()
    await pilot.press("f")
    await confirm(pilot, app, "y")
    assert await settle(pilot, lambda: "download failed" in log_text(b), tries=200), log_text(b)
    assert not cached.exists(), "a truncated download was kept"
    (TMP / "tiny").unlink()
    print("PASS a truncated frida-server download is rejected, not cached")

    # One version's worth of cache: a build for a frida that has since been
    # upgraded past will never be pushed again, and each is tens of megabytes.
    stale = moabile.CACHE / "frida-server-16.0.1-android-arm64"
    stale.write_bytes(b"an older server")
    await pilot.press("f")
    await confirm(pilot, app, "y")
    assert await settle(pilot, lambda: cached.exists(), tries=200), log_text(b)
    assert not stale.exists(), "an old frida-server was left in the cache"
    print("PASS the frida-server cache keeps one version, not every version")

    # p is stop plus delete: nothing of ours is left at /data/local/tmp, socket
    # directory included, and n leaves the device exactly as it was.
    assert await settle(pilot, lambda: (TMP / "frida-up").exists(), tries=200), log_text(b)
    (TMP / "edits").write_text("")
    await pilot.press("p")
    await confirm(pilot, app, "n")
    assert await settle(pilot, lambda: not isinstance(app.screen, moabile.ConfirmScreen)), \
        app.screen
    assert (TMP / "frida-up").exists(), "n took the server down anyway"
    assert "rm -rf" not in (TMP / "edits").read_text(), (TMP / "edits").read_text()
    await pilot.press("p")
    await confirm(pilot, app, "y")
    assert await settle(pilot, lambda: "removed" in log_text(b), tries=200), log_text(b)
    assert not (TMP / "frida-up").exists(), "p left the server running"
    edits = (TMP / "edits").read_text()
    assert "/data/local/tmp/frida-server" in edits and "re.frida.server" in edits, edits
    print("PASS p stops frida-server and takes it off the device")


async def phase_ios(app, pilot) -> None:
    """the jailbroken iPhone: usbmux for the device, ssh for everything inside.

    Runs last of the device phases and cleans up after itself, so the two
    android panels the phases before it work on are still the only ones open.
    """
    (TMP / "ios").touch()
    await app.refresh_devices()
    assert await settle(pilot, lambda: IOS_UDID in app.serials), app.serials
    assert app.kinds[IOS_UDID] == "ios", app.kinds
    # A udid is forty characters and the sidebar is thirty-four wide, so the
    # row shows the ends of it rather than wrapping onto a second line.
    rows = [str(node.query_one(Label).render())
            for node in app.query_one("#devices", ListView)._nodes]
    assert any("0000803000…BBCC" in row for row in rows), rows

    await app.toggle_panel(IOS_UDID)
    ios = app.panel(IOS_UDID)
    assert isinstance(ios, moabile.IosPanel), type(ios)
    assert await settle(pilot, lambda: ios.props.get("ProductType") == "iPhone14,2",
                        tries=300), ios.props
    # The device name carries "[/]", the same trap as an android model name.
    assert ios.props["DeviceName"] == "Test iPhone [/] [bold]", ios.props["DeviceName"]
    # The log and the screen with it: "root: False" on its own says nothing
    # about which of the tunnel, the master and sudo did not answer, and a
    # modal still up waiting for a password looks exactly the same from here.
    assert ios.root and ios.jb == "", (ios.root, ios.jb, app.screen, log_text(ios)[-400:])
    assert ios.ssh_port == moabile.IOS_SSH_PORT, \
        f"{ios.ssh_port}: is a second copy of this suite running," \
        f" or something else holding port {moabile.IOS_SSH_PORT}?"
    assert f"2222:22 -u {IOS_UDID}" in (TMP / "iproxy-log").read_text(), "no usb tunnel"
    assert "ssh: root" in log_text(ios), log_text(ios)
    # And the same cut in the panel border and in the file browser's heading:
    # it was sixteen characters off the front there and twelve here, which on a
    # udid is the half that is the same on every iPhone of that model.
    assert ios.border_title is not None and ios.border_title.startswith("0000803000…BBCC"), ios.border_title
    print("PASS an iphone is found over usbmux and answers over the tunnel")

    # Until the trust dialog is accepted, lockdownd answers nothing — which is
    # a dialog on the phone, not a fault here, and worth saying as much.
    (TMP / "ios-untrusted").touch()
    await ios.describe()
    assert not ios.props, ios.props
    assert "accept the trust dialog" in log_text(ios), log_text(ios)
    (TMP / "ios-untrusted").unlink()
    await ios.describe()                         # trusted again
    assert ios.props.get("ProductType") == "iPhone14,2", ios.props
    print("PASS a phone that has not been trusted is told to accept the dialog")

    await ios.refresh_stats()
    stats = _stats(ios)
    # battery over usbmux, the rest down the one multiplexed ssh connection.
    assert "77%" in stats and "192.168.1.77" in stats and "0.55" in stats, stats
    assert "3.2/4.3 GB" in stats, stats          # hw.memsize minus the free pages
    assert "syslog" in stats and "ioscpy" in stats, stats
    assert "pid" in stats, stats
    # A pid is the first field of a line. Any digit anywhere used to do, and a
    # shell with no ps answered "sh: 1: ps: not found" — reported as pid 1.
    (TMP / "ios-noprocps").touch()
    assert (await ios.frida_pid()) is None, await ios.frida_pid()
    now = await ios.stats()
    assert now["frida"] == "", now
    (TMP / "ios-noprocps").unlink()
    print("PASS a shell that cannot find ps is not mistaken for frida on pid 1")

    # Reading the load, the memory and the address needs nothing mobile does
    # not already have, and those are what the poll asks for every three
    # seconds: no sudo, so a phone without it still fills the stats line.
    (TMP / "ssh-log").write_text("")
    now = await ios.stats()
    assert (now["load"], now["ip"]) == ("0.55", "192.168.1.77"), now
    assert "sudo" not in (TMP / "ssh-log").read_text(), (TMP / "ssh-log").read_text()
    print("PASS the stats poll reads without asking for root")

    # sysctl, vm_stat and ifconfig live under /usr/sbin and /var/jb, which a
    # non-interactive ssh does not always have on its PATH — and when they are
    # not found the line said ? three times with nothing to say why.
    (TMP / "ssh-log").write_text("")
    await ios.stats()
    assert "/var/jb/usr/sbin" in (TMP / "ssh-log").read_text(), "no PATH for the phone's tools"
    (TMP / "ios-nopath").touch()
    now = await ios.stats()
    assert (now["load"], now["mem"], now["ip"]) == ("?", "?", "?"), now
    stats_said = log_text(ios).count("stats unavailable")
    assert stats_said == 1 and "sysctl: not found" in log_text(ios), log_text(ios)
    await ios.stats()               # every three seconds, so it is said once
    assert log_text(ios).count("stats unavailable") == 1, log_text(ios)
    (TMP / "ios-nopath").unlink()
    now = await ios.stats()
    assert (now["load"], now["ip"]) == ("0.55", "192.168.1.77"), now
    (TMP / "ios-nopath").touch()    # and again after it has worked since
    await ios.stats()
    assert log_text(ios).count("stats unavailable") == 2, log_text(ios)
    (TMP / "ios-nopath").unlink()
    print("PASS stats that cannot be read say why, once, instead of three ?")

    # ipconfig is on no jailbreak worth counting on, so the address comes off
    # ifconfig — a tab-indented line, among inet6 addresses that are not it.
    (TMP / "ios-ifconfig").touch()
    now = await ios.stats()
    assert now["ip"] == "10.0.0.5", now
    assert "ifconfig -a" in (TMP / "ssh-log").read_text(), "no ifconfig fallback"
    (TMP / "ios-ifconfig").unlink()
    # scutil is the third try, for a phone that has neither of the other two.
    (TMP / "ios-scutil").touch()
    now = await ios.stats()
    assert now["ip"] == "10.1.2.3", now
    assert "scutil --nwi" in (TMP / "ssh-log").read_text(), "no scutil fallback"
    (TMP / "ios-scutil").unlink()
    # With wifi off there is no address to read, and down the usb tunnel there
    # is none to have: the row says how the phone is plugged in instead, and
    # nothing is logged — there is nothing there to fix.
    (TMP / "ios-noip").touch()
    now = await ios.stats()
    assert now["ip"] == "usb" and now["load"] == "0.55", now
    assert "no address" not in log_text(ios), log_text(ios)
    (TMP / "ios-noip").unlink()
    # A phone with none of those commands is answered from this machine's arp
    # table instead, by the wifi MAC lockdownd hands out over usbmux.
    (TMP / "ios-noipcmd").touch()
    (TMP / "ios-poll").write_text("0")       # the next poll is an odd one
    (TMP / "arp-log").write_text("")
    ios._arp_due = 0
    now = await ios.stats()
    assert now["ip"] == "10.9.9.9", now
    # Nothing in the log: the row has a real address, so there is nothing to
    # explain — the line is for a row that ends up with nothing at all.
    assert "no address" not in log_text(ios), log_text(ios)
    # Six more polls, with the phone's stderr landing in a different section
    # every other one — ssh folds it in wherever it arrives. The row has to
    # hold still: reading each poll on its own flickered it between the address
    # and usb. And the arp table is asked once every BATTERY_TICKS polls, not
    # every three seconds.
    for _ in range(6):
        assert (await ios.stats())["ip"] == "10.9.9.9", "the row flickered"
    assert (TMP / "arp-log").read_text().count("neigh") == 1, (TMP / "arp-log").read_text()

    # And when the arp table has nothing either: usb, and nothing said. Which
    # of the four commands this jailbreak left out is not something anybody can
    # act on, and the row already says what there is — the cable.
    (TMP / "no-arp").touch()
    ios._arp, ios._arp_due = "", 0
    ios.query_one(RichLog).clear()
    now = await ios.stats()
    assert now["ip"] == "usb", now
    assert "not found" not in log_text(ios), log_text(ios)
    assert "no address" not in log_text(ios), log_text(ios)
    (TMP / "ssh-log").write_text("")
    for _ in range(6):
        assert (await ios.stats())["ip"] == "usb", "the row flickered"
    assert log_text(ios) == "", log_text(ios)
    # And it stops asking: four commands the phone does not have are four
    # failed execs on it every three seconds. The marker stays, because its
    # absence is how address() tells "no address" from "never asked".
    ssh_log = (TMP / "ssh-log").read_text()
    assert "ipconfig getifaddr" not in ssh_log, ssh_log[:300]
    assert "echo @ip;" in ssh_log, ssh_log[:300]

    # A phone reached over the network instead of the tunnel needs no command
    # on it at all: that host is the address.
    was = ios.ssh_host
    ios.ssh_host = "192.168.1.9"
    now = await ios.stats()
    assert now["ip"] == "192.168.1.9", now
    # But not when the batch never ran: one row claiming to know something
    # while the rest say ? is worse than the ?.
    assert await ios.address({}) == "?", await ios.address({})
    ios.ssh_host = was
    (TMP / "no-arp").unlink()
    (TMP / "ios-noipcmd").unlink()
    # And having stopped asking, it stays stopped: the panel is not sending the
    # four any more, so a phone that grows one of them back is not noticed for
    # as long as this panel is open. That is the trade the row is here for —
    # four failed execs every three seconds against a reading that does not
    # change on a phone — and closing the panel is what starts it over.
    now = await ios.stats()
    assert now["ip"] == "usb", now
    ios._no_ip_tool = False                  # what reopening the panel does
    now = await ios.stats()
    assert now["ip"] == "192.168.1.77", now
    print("PASS four tries, then arp, then usb — and the reason said once")

    # The battery is the one reading that does not come down the ssh
    # connection: it is a fresh usbmux round trip for a number that does not
    # move in three seconds, so it is read once every BATTERY_TICKS polls and
    # kept in between.
    (TMP / "battery-log").write_text("")
    ios._batt_due = 0
    for _ in range(3):
        await ios.stats()
    assert (TMP / "battery-log").read_text().count("batt") == 1, \
        (TMP / "battery-log").read_text()
    print("PASS the ios stats line is one usbmux call and one ssh round trip")

    # All applications listed (--all / list_all) so that TrollStore apps
    # (registered as system apps) appear, with com.apple.* filtered out.
    assert await settle(pilot, lambda: ios.packages == ["com.target.ios"]), ios.packages
    installer = (TMP / "installer-log").read_text()
    assert "--all" in installer or "list_all" in installer, installer
    assert "CFBundleExecutable" in installer, installer
    # And the command line before `list` existed: -l -o list_all, three fixed columns.
    with patch.dict(moabile._HELP, {("ideviceinstaller", "--install"): True}):
        (TMP / "installer-log").write_text("")
        await ios.load_packages()
        assert "list_all" in (TMP / "installer-log").read_text(), \
            (TMP / "installer-log").read_text()
        assert ios.packages == ["com.target.ios"], ios.packages
        assert not ios.executables and not ios.bundles, (ios.executables, ios.bundles)
    await ios.load_packages()                    # back to the current shape
    assert ios.executables["com.target.ios"] == "Target", ios.executables

    # TrollStore app test: non-Apple system app is preserved, while Apple apps are dropped
    (TMP / "ios-trollstore").touch()
    await ios.load_packages()
    assert "com.opa334.TrollStore" in ios.packages, ios.packages
    assert "com.apple.mobilesafari" not in ios.packages, ios.packages
    (TMP / "ios-trollstore").unlink()
    await ios.load_packages()
    # And the line when nothing comes back at all, which is the same answer the
    # android side gives when pm lists nothing: check that the tool reaches it.
    (TMP / "ios-noapps").touch()
    await ios.load_packages()
    assert ios.packages == [], ios.packages
    assert "no apps listed" in log_text(ios), log_text(ios)
    (TMP / "ios-noapps").unlink()
    await ios.load_packages()
    assert ios.packages == ["com.target.ios"], ios.packages
    ios.package = "com.target.ios"
    # Picking an app looks its bundle up once: iOS runs it as the executable
    # inside the bundle, which is both the syslog filter and the pid.
    await ios.package_chosen()
    assert ios.proc_name == "Target", ios.proc_name
    (TMP / "ios-running").touch()
    now = await ios.stats()
    assert now["pid"] == "4321", now          # off the process table, by path
    (TMP / "ios-running").unlink()
    now = await ios.stats()
    assert now["pid"] == "-", now
    print("PASS the ios stats line has the app's pid, by the executable it runs as")

    ios.focus()
    await pilot.pause()

    # And the server in that package is inert without the agent: one on the
    # phone without the other is not something to offer to start, because it
    # comes up, holds the port and cannot inject, with nothing saying why.
    (TMP / "ios-server-there").touch()
    assert (await ios.server_bytes()) is None, "a server with no agent was offered"
    (TMP / "ios-agent-there").touch()
    assert (await ios.server_bytes()) == 20971520, await ios.server_bytes()
    (TMP / "ios-server-there").unlink()
    (TMP / "ios-agent-there").unlink()
    print("PASS a frida-server with no agent beside it is not offered to start")

    # frida has published no bare ios binary for some time: it is a .deb, and
    # the server in it is inert without the agent that ships beside it.
    unpacked = moabile.CACHE / "frida-16.5.9-iphoneos-arm64"
    shutil.rmtree(unpacked, ignore_errors=True)
    (TMP / "scp-log").write_text("")
    await pilot.press("f")
    await confirm(pilot, app, "y")
    assert await settle(pilot, lambda: "is up, pid 9101" in log_text(ios), tries=300), log_text(ios)
    install = log_text(ios)
    # arm64e is an arm64 build: frida publishes no arm64e package.
    # And the build is named the way frida's own releases name it, which is
    # what the .deb fetched below is called.
    assert "iphoneos-arm64" in install and "arm64e" in install, install
    assert "iphoneos-arm64.deb" in (TMP / "curl-log").read_text(), (TMP / "curl-log").read_text()
    assert "unpack  2 files" in install, install
    pushed = (TMP / "scp-log").read_text()
    assert "/usr/sbin/frida-server" in pushed, pushed
    assert "/usr/lib/frida/frida-agent.dylib" in pushed, pushed
    assert (unpacked / "var/jb/usr/sbin/frida-server").is_file(), list(unpacked.rglob("*"))
    await ios.refresh_stats()
    assert "frida ● 9101" in _stats(ios), _stats(ios)
    # And the list is the same with a server up as without one: it comes off
    # the installer, and frida-ps is not asked at all.
    await ios.load_packages()
    assert ios.packages == ["com.target.ios"], ios.packages
    assert not (TMP / "frida-ps-log").exists(), (TMP / "frida-ps-log").read_text()
    print("PASS frida-server is pushed over scp and started over ssh")

    # A rootless jailbreak keeps its own userland under /var/jb, which is where
    # frida-server and its agent have to go — and what p has to take away
    # again. A rootful one has the same paths at the root.
    (TMP / "rootless").touch()
    await ios.describe()
    assert ios.jb == "/var/jb", ios.jb
    assert "rootless jailbreak" in log_text(ios), log_text(ios)
    paths = await ios.server_files("16.5.9", "arm64")
    assert paths is not None and [remote for _local, remote in paths] == [
        "/var/jb/usr/sbin/frida-server",
        "/var/jb/usr/lib/frida/frida-agent.dylib"], paths
    assert ios.server_junk == "/var/jb/usr/lib/frida", ios.server_junk
    (TMP / "rootless").unlink()
    await ios.describe()
    assert ios.jb == "", ios.jb
    paths = await ios.server_files("16.5.9", "arm64")
    assert paths is not None and [remote for _local, remote in paths] == [
        "/usr/sbin/frida-server", "/usr/lib/frida/frida-agent.dylib"], paths
    print("PASS a rootless jailbreak puts frida under /var/jb, a rootful one at the root")

    await pilot.press("t")
    assert await settle(pilot, lambda: ios.term.argv[:1] == ["ssh"], tries=200), ios.term.argv
    assert "mobile@127.0.0.1" in ios.term.argv, ios.term.argv
    assert "BatchMode=yes" not in ios.term.argv, "an interactive shell cannot refuse a password"
    ios.term.stop()
    await pilot.pause(0.2)
    print("PASS t opens an ssh session down the tunnel, password prompt allowed")

    (TMP / "ios-running").touch()                # so there is a pid to pin to
    (TMP / "syslog-log").write_text("")
    await pilot.press("l")
    await confirm(pilot, app)                    # only the selected app
    assert await settle(pilot, lambda: "syslog" in ios.streams, tries=200), ios.streams
    # The pid, and the tool asked for no filter at all: -p is idevicesyslog's
    # only one and it matches names, so passing one takes the stream away
    # before this side sees a line of it — and a name is the thing that
    # matches a process merely called something similar.
    assert ios.log_keep == "[4321]", ios.log_keep
    assert await settle(pilot, lambda: "running" in log_text(ios), tries=200), log_text(ios)
    assert "-p" not in (TMP / "syslog-log").read_text(), (TMP / "syslog-log").read_text()
    # What another process said never reaches the panel.
    assert "not the app" not in log_text(ios), log_text(ios)
    assert "filtering on pid 4321" in log_text(ios), log_text(ios)
    await ios.refresh_stats()
    assert "syslog ●" in _stats(ios), _stats(ios)
    await pilot.press("l")
    assert await settle(pilot, lambda: "syslog" not in ios.streams), ios.streams

    # A filter that keeps nothing looks exactly like a device with nothing to
    # say, and on this relay it is usually neither: most of what an app logs
    # never arrives here at all. Said once, after enough has gone by to mean it.
    (TMP / "ios-syslog-noise").touch()
    await pilot.press("l")
    await confirm(pilot, app)
    assert await settle(pilot, lambda: "none from [4321]" in log_text(ios), tries=400), \
        log_text(ios)
    assert "noise 1" not in log_text(ios), log_text(ios)
    await pilot.press("l")
    assert await settle(pilot, lambda: "syslog" not in ios.streams), ios.streams
    (TMP / "ios-syslog-noise").unlink()

    # Whole device: nothing is dropped, the other process included.
    await pilot.press("l")
    await confirm(pilot, app, "n")
    assert await settle(pilot, lambda: "not the app" in log_text(ios), tries=200), log_text(ios)
    assert ios.log_keep == "", ios.log_keep
    await pilot.press("l")
    assert await settle(pilot, lambda: "syslog" not in ios.streams), ios.streams

    # With the app stopped there is no pid, and the same answer as the android
    # side gives: no question, the whole device, one line saying why. The
    # tool's own -p is never used — it matches process *names*, so a second
    # process called something similar comes with it, and it takes the stream
    # away before this side sees a line of it.
    (TMP / "ios-running").unlink()
    (TMP / "syslog-log").write_text("")
    await pilot.press("l")
    assert await settle(pilot, lambda: "syslog" in ios.streams, tries=200), ios.streams
    assert not isinstance(app.screen, moabile.ConfirmScreen), "asked with no pid to answer"
    assert ios.log_keep == "", ios.log_keep
    assert "-p" not in (TMP / "syslog-log").read_text(), (TMP / "syslog-log").read_text()
    assert "no pid for com.target.ios" in log_text(ios), log_text(ios)
    await pilot.press("l")
    assert await settle(pilot, lambda: "syslog" not in ios.streams), ios.streams
    print("PASS the ios syslog is pinned to a pid here, and to nothing at the tool")

    iosfiles = TMP / "iosfiles"
    iosfiles.mkdir(exist_ok=True)
    ios.local_dir = str(iosfiles)
    await pilot.press("d")
    assert await on_screen(pilot, app, moabile.FilesScreen), app.screen
    files = app.screen
    entries = files.device.query_one(ListView)
    assert await settle(pilot, lambda: [n.value for n in entries._nodes]
                        == ["Library/", "Media/", "note-ios.txt"]), \
        [n.value for n in entries._nodes]
    entries.focus()
    select(entries, "note-ios.txt")
    await confirm(pilot, app)
    assert await settle(pilot, lambda: (iosfiles / "note-ios.txt").exists(), tries=300), \
        log_text(ios)
    assert "pulled-from-/var/mobile/note-ios.txt" in (iosfiles / "note-ios.txt").read_text()
    # One tar stream, not scp: a bundle is hundreds of files with symlinks in
    # it, and scp on top of sftp resolves those instead of copying them.
    # MASTG-TECH-0053 stages the archive in /tmp on the phone; this pipes it,
    # so the device is left exactly as it was found.
    ssh_log = (TMP / "ssh-log").read_text()
    assert "tar cf - -C /var/mobile note-ios.txt" in ssh_log, ssh_log[-400:]
    assert ":/var/mobile/note-ios.txt" not in (TMP / "scp-log").read_text(), \
        "a pull still went through scp"
    # The same two keys go out as ssh commands rather than adb ones. The
    # index, not select(): activating the row would send the file again.
    entries.focus()
    entries.index = [n.value for n in entries._nodes].index("note-ios.txt")
    (TMP / "ios-edits").write_text("")           # so the wait below can read it
    await pilot.press("d")
    await confirm(pilot, app)
    assert await settle(pilot, lambda: "rm -f /var/mobile/note-ios.txt"
                        in (TMP / "ios-edits").read_text(), tries=300), \
        (TMP / "ios-edits").read_text()
    # MASTG-TECH-0059: the Data container, whose uuid is not the bundle's and
    # which nothing on the phone names after the app.
    await pilot.press("a")
    assert await settle(pilot, lambda: files.device.path
                        == "/var/mobile/Containers/Data/Application/CC-DD", tries=300), \
        files.device.path
    assert "metadata.plist" in (TMP / "ssh-log").read_text(), "the container was not looked up"
    print("PASS a finds the ios data container, which is not the bundle")

    await pilot.press("escape")
    assert await settle(pilot, lambda: not isinstance(app.screen, moabile.FilesScreen))
    print("PASS the file browser reaches the phone over ssh, both directions")

    await pilot.press("i")
    assert await settle(pilot, lambda: "jailbreak" in log_text(ios), tries=200), log_text(ios)
    info = log_text(ios)
    assert "Darwin iPhone" in info and "iPhone14,2" in info and "Sileo" in info, info
    # The frida row is a pid, not the process table it was read out of: the
    # table is how the phone answers without grep, and it is three hundred
    # lines long on a real one.
    assert re.search(r"frida\s+(pid \d+|not running)", info), info
    assert "backboardd" not in info, "the whole process table landed in the log"
    # The net row the android dump has had all along: one summary read one way
    # on both families. A phone without ipconfig gets the `-` every other row
    # here gets for a command the device has not got, not a forty-line dump.
    assert re.search(r"net\s+192\.168\.1\.77", info), info
    (TMP / "ios-noipcmd").touch()
    ios.query_one(RichLog).clear()
    await ios.system_info()
    assert re.search(r"net\s+-", log_text(ios)), log_text(ios)
    (TMP / "ios-noipcmd").unlink()
    print("PASS i dumps what the phone is, over usbmux and ssh together")

    ipas = TMP / "ipas"
    ipas.mkdir(exist_ok=True)
    (ipas / "target.ipa").write_text("PK")
    (ipas / "notes.txt").write_text("not an ipa")
    ios.local_dir = str(ipas)
    # ideviceinstaller reports a refusal with an exit status of 0.
    (TMP / "badipa").touch()
    app.action_install()
    assert await on_screen(pilot, app, moabile.ScriptScreen), app.screen
    picked = app.screen.side.query_one(ListView)
    assert await settle(pilot, lambda: [n.value for n in picked._nodes] == ["target.ipa"]), \
        [n.value for n in picked._nodes]
    select(picked, "target.ipa")
    await confirm(pilot, app)
    assert await settle(pilot, lambda: "APIInternalError" in log_text(ios),
                        tries=300), log_text(ios)
    (TMP / "badipa").unlink()
    app.action_install()
    assert await on_screen(pilot, app, moabile.ScriptScreen), app.screen
    select(app.screen.side.query_one(ListView), "target.ipa")
    await confirm(pilot, app)
    assert await settle(pilot, lambda: "Install: Complete" in log_text(ios),
                        tries=300), log_text(ios)
    assert f"install {ipas}/target.ipa" in (TMP / "installer-log").read_text()
    # The refusal every unsigned ipa gets, including one repacked off a phone
    # by this very tool: nothing here can sign an app, so the message points at
    # the one thing on the device that makes it installable anyway.
    (TMP / "unsigned").touch()
    rc, out = await ios.install(f"{ipas}/target.ipa")
    assert rc != 0, out
    assert "AppSync Unified" in out, out
    (TMP / "unsigned").unlink()
    print("PASS an unsigned ipa is refused with the reason, not just a code")

    app.action_save_app()
    assert await on_screen(pilot, app, moabile.ScriptScreen), app.screen
    assert app.screen.pick_dir
    await pilot.press("s")
    ipa = ipas / "com.target.ios.ipa"
    assert await settle(pilot, lambda: ipa.exists(), tries=400), log_text(ios)
    with zipfile.ZipFile(ipa) as archive:
        names = archive.namelist()
    # An ipa is the bundle under Payload/, zipped on the host: nothing was
    # asked of the phone but a copy.
    assert "Payload/Target.app/Target" in names, names
    assert "Payload/Target.app/Info.plist" in names, names
    assert "tar cf - -C /var/containers/Bundle/Application/AA-BB Target.app" \
        in (TMP / "ssh-log").read_text(), "the bundle was not streamed out as one archive"
    assert "encrypted" in log_text(ios), log_text(ios)

    # Overwrite confirmation test for iOS
    app.action_save_app()
    assert await on_screen(pilot, app, moabile.ScriptScreen)
    await pilot.press("s")
    assert await on_screen(pilot, app, moabile.ConfirmScreen)
    await pilot.press("n")
    assert await settle(pilot, lambda: "export cancelled" in log_text(ios)), log_text(ios)
    print("PASS the installed bundle comes back as an ipa, repacked on the host")

    # And one that is not on the phone: the search over the Info.plists finds
    # nothing, and e says which two places it looked rather than failing bare.
    (TMP / "ios-nobundle").touch()
    kept_bundles, ios.bundles = ios.bundles, {}
    await ios.save_app(str(ipas))
    assert "no bundle on this phone" in log_text(ios), log_text(ios)
    ios.bundles = kept_bundles
    (TMP / "ios-nobundle").unlink()
    print("PASS an app that is not installed is said to be missing, not repacked")

    # And nowhere to stage the bundle: the same rule as the cache above, on the
    # other end of e. A full or read-only temporary directory is a line in the
    # panel, not an exception out of a worker.
    kept_mkdtemp = moabile.tempfile.mkdtemp

    def no_room(**_kw: object) -> str:
        raise OSError(28, "No space left on device")

    moabile.tempfile.mkdtemp = no_room  # type: ignore[assignment]
    try:
        await ios.save_app(str(ipas))
    finally:
        moabile.tempfile.mkdtemp = kept_mkdtemp
    assert "nowhere to stage" in log_text(ios), log_text(ios)
    print("PASS a temporary directory that cannot be made is not a crash either")

    # A phone with no grep on it looks exactly like one where the app is not
    # installed — and says nothing at all, because the 2>/dev/null that keeps
    # the unmatched globs quiet swallows the shell's "not found" too. The 127
    # is what tells the two apart, and the panel has to name the phone's
    # missing tool rather than blame the app.
    (TMP / "ios-nogrep").touch()
    ios.said_ok("grep")
    kept_bundles, ios.bundles = ios.bundles, {}
    assert await ios.bundle_dir() == "", log_text(ios)
    assert "no grep on the phone" in log_text(ios), log_text(ios)
    ios.bundles = kept_bundles
    (TMP / "ios-nogrep").unlink()
    print("PASS a phone with no grep says so, rather than reading as an app that is gone")

    app.action_mirror()
    assert await settle(pilot, lambda: ios.mirror is not None), log_text(ios)
    window = ios.mirror
    assert "ioscpy" in log_text(ios), log_text(ios)
    app.action_mirror()
    assert await settle(pilot, lambda: ios.mirror is None), log_text(ios)
    assert window is not None and window.returncode is not None, "the ioscpy window was left unreaped"
    print("PASS w mirrors the phone with ioscpy and closes it again")

    # objection needs the app running, and nothing on the phone maps a bundle
    # id to a pid: the launch goes through open(1) and the check through the
    # process table, by the executable inside the bundle.
    (TMP / "ios-running").unlink(missing_ok=True)
    assert (await ios.app_pid()) is None, "a stopped app reported a pid"
    assert await ios.launch_app(), "a launch that worked was reported as a failure"
    assert "open com.target.ios" in (TMP / "ios-open").read_text()
    assert (await ios.app_pid()) == "4321", await ios.app_pid()

    # A phone without uikittools has no open at all. That is not a failure of
    # the app and not anything to fix from here, so nothing goes on screen:
    # the answer is "this phone cannot", and the caller is the one that says
    # what to do instead. No second go through sudo either — a command that is
    # not there is not there for root.
    (TMP / "ios-running").unlink(missing_ok=True)
    (TMP / "ios-noopen").touch()
    (TMP / "ssh-log").write_text("")
    ios.query_one(RichLog).clear()
    assert not await ios.launch_app(), "a phone with no open reported a launch"
    assert log_text(ios) == "", log_text(ios)
    open_asked = [ln for ln in (TMP / "ssh-log").read_text().splitlines() if "open com.target" in ln]
    assert len(open_asked) == 1 and "sudo" not in open_asked[0], open_asked
    (TMP / "ios-noopen").unlink()
    # The same phone, saying nothing about it: a shell that puts its "not
    # found" where this end cannot read it still exits 127, and 127 is a
    # command that could not be run — not a refusal worth two lines of screen.
    (TMP / "ios-open-gone").touch()
    ios.query_one(RichLog).clear()
    assert not await ios.launch_app(), "a phone with no open reported a launch"
    assert log_text(ios) == "", log_text(ios)
    (TMP / "ios-open-gone").unlink()
    # A refusal with nothing to say is still a refusal: reported for what it
    # was, rather than swallowed for having printed no reason.
    (TMP / "ios-open-mute").touch()
    assert not await ios.launch_app(), "a refused open was reported as a launch"
    open_said = log_text(ios)
    assert "open com.target.ios: exited 3" in open_said, open_said[-200:]
    assert "sudo open: exited 3" in open_said, open_said[-200:]
    assert (await ios.app_pid()) is None, "the app came up on a refused open"
    (TMP / "ios-open-mute").unlink()
    # And a phone that keeps open out of mobile's reach: refused first, then
    # started — and both halves said, rather than five seconds of nothing.
    # Launching an app is SpringBoard's job and SpringBoard is mobile's, so
    # open(1) is asked as the login user and only then through sudo — asked as
    # root first, it came back a success that launched nothing, and objection
    # had no process to attach to unless frida had spawned the app already.
    (TMP / "ios-open-needs-root").touch()
    (TMP / "ssh-log").write_text("")
    assert await ios.launch_app(), "the sudo launch was reported as a failure"
    assert "Operation not permitted" in log_text(ios), log_text(ios)
    open_asked = [ln for ln in (TMP / "ssh-log").read_text().splitlines() if "open com.target" in ln]
    assert len(open_asked) == 2, open_asked
    assert "sudo" not in open_asked[0] and "sudo" in open_asked[1], open_asked
    assert (await ios.app_pid()) == "4321", await ios.app_pid()
    (TMP / "ios-open-needs-root").unlink()
    print("PASS the app is launched as the login user, and through sudo only if refused")
    # And it resolves the executable again when what it has is for another
    # app. Off the app list, so it costs nothing on the phone.
    ios._proc_for, ios.proc_name = None, ""
    (TMP / "ssh-log").write_text("")
    assert (await ios.app_pid()) == "4321", await ios.app_pid()
    assert ios.proc_name == "Target", ios.proc_name
    assert "grep -ls" not in (TMP / "ssh-log").read_text(), "the phone was searched anyway"
    # The search is the fallback for an installer too old to be asked for the
    # attribute, and then it happens once per app picked, not once per call:
    # objection asks ten times while it waits for the app to come up.
    kept, keptb = ios.executables, ios.bundles
    ios.executables, ios.bundles = {}, {}
    ios._proc_for, ios.proc_name = None, ""
    (TMP / "ssh-log").write_text("")
    assert (await ios.app_pid()) == "4321", await ios.app_pid()
    assert ios.proc_name == "Target", ios.proc_name
    assert (TMP / "ssh-log").read_text().count("grep -ls") == 1, (TMP / "ssh-log").read_text()
    await ios.app_pid()
    assert (TMP / "ssh-log").read_text().count("grep -ls") == 1, "the bundle was looked up twice"
    ios.executables, ios.bundles = kept, keptb
    print("PASS a stopped app is started with open(1) and found in the process table")

    # And that pid is what objection is given. The bundle id sends it through
    # frida's application list, which carries a pid only for an app frida is
    # already holding — on a phone that meant objection worked only after the
    # frida client had spawned the app once, and exited 1 every other time.
    (TMP / "ios-open").write_text("")
    app.action_objection()
    assert await settle(pilot, lambda: ios.term.argv[:1] == ["objection"], tries=300), ios.term.argv
    assert ios.term.argv == ["objection", "-S", IOS_UDID, "-n", "4321", "start"], ios.term.argv
    assert "com.target.ios" in ios.term.label, ios.term.label
    # A pid is not enough on this family: iOS suspends an app that is off
    # screen, and attaching to a suspended process is a prompt that never
    # arrives. So it is brought to the front first — and nothing is said about
    # it, because there is nothing for anybody to do once it is on screen.
    assert "open com.target.ios" in (TMP / "ios-open").read_text(), \
        "the app was never brought to the front"
    assert "on the phone" not in log_text(ios), log_text(ios)

    # And on a phone with no open, the one thing worth interrupting for: only
    # the person holding it can put the app back on screen. Said in our own
    # words — what the shell called the missing command helps nobody.
    (TMP / "ios-noopen").touch()
    ios.query_one(RichLog).clear()
    await ios.wake_app()
    assert "open com.target.ios on the phone" in log_text(ios), log_text(ios)
    assert "not found" not in log_text(ios), log_text(ios)

    # Same phone, app not running: o has no way to start it and nothing to
    # wait for, so it says which of the two the person at the keyboard has to
    # do. Ten seconds of polling a process table would have been the old
    # answer, and "would not start" the wrong reason for it.
    (TMP / "ios-running").unlink(missing_ok=True)
    began = time.monotonic()
    app.action_objection()
    assert await settle(pilot, lambda: "cannot be started from here" in log_text(ios),
                        tries=200), log_text(ios)
    assert time.monotonic() - began < 5, "waited for a launch that was never asked for"
    assert "not found" not in log_text(ios), log_text(ios)
    (TMP / "ios-noopen").unlink()
    (TMP / "ios-running").touch()
    ios.term.stop()
    await pilot.pause()
    print("PASS objection on the phone attaches to a pid, not to a bundle id")

    await pilot.press("f")                       # frida-server off again
    assert await settle(pilot, lambda: "frida-server stopped" in log_text(ios), tries=300), \
        log_text(ios)
    assert not (TMP / "ios-frida").exists(), "kill -9 never reached the server"

    # A tunnel that will not come up is asked for again by every status poll.
    # Saying so each time buried the panel under an error toast every three
    # seconds, so it is reported once and retried quietly.
    (TMP / "iproxy-dies").touch()
    ios.said_ok("tunnel-down")
    assert ios.tunnel is not None, "the panel never opened a tunnel"
    ios.tunnel.terminate()
    ios.tunnel.wait()
    for _ in range(3):
        assert not await ios.tunnel_up(), "a dead iproxy still reported a tunnel"
    assert log_text(ios).count("iproxy exited at once") == 1, log_text(ios)
    (TMP / "iproxy-dies").unlink()
    assert await ios.tunnel_up(), log_text(ios)
    # And one that comes up and then dies is restarted by the next poll, which
    # used to log its command line each time. The command line once per port,
    # the flapping once, and nothing after that.
    was_count = log_text(ios).count("$ iproxy")
    for _ in range(4):
        ios.tunnel.terminate()
        ios.tunnel.wait()
        assert await ios.tunnel_up(), log_text(ios)
    assert log_text(ios).count("$ iproxy") == was_count, log_text(ios)
    assert log_text(ios).count("keeps dropping") == 1, log_text(ios)
    print("PASS a tunnel that will not come up is reported once, not every poll")
    print("PASS a tunnel that flaps is restarted quietly, and said once")

    # Everything below drives the ssh login by hand, so the status poll is
    # held off: two callers asking for one connection at the same moment is a
    # race the app serialises but a test cannot observe.
    app._ticking = True
    # A tunnel some earlier run left behind holds the port, and the port is
    # remembered per device: retrying it every poll is how "iproxy exited at
    # once" turned into a phone that never came back.
    # An ephemeral port the kernel picks, so two of these suites running at
    # once do not fight over one number: what is under test is that a port
    # already held gets stepped over, not which port that is.
    blocker = socket.socket()
    blocker.bind(("127.0.0.1", 0))
    blocker.listen(1)
    taken = blocker.getsockname()[1]
    try:
        await ios.drop_tunnel()
        ios.ssh_port = taken                     # as if this were what was remembered
        assert await ios.tunnel_up(), log_text(ios)
        assert ios.ssh_port != taken, f"the taken port {taken} was used anyway"
    finally:
        blocker.close()
    print("PASS a local port already taken is stepped over, not retried forever")

    # Two questions about a port, and only one of them may be asked while
    # iproxy is binding it: a probe that binds, even for the instant it takes
    # to fail, takes the port away from iproxy — which came back as "iproxy
    # exited at once", telling whoever was there to go and unlock a phone that
    # had nothing to do with it.
    spare_probe = socket.socket()
    spare_probe.bind(("127.0.0.1", 0))
    spare = spare_probe.getsockname()[1]
    spare_probe.close()
    assert moabile.port_free(spare) and not moabile.port_listening(spare), spare
    held = socket.socket()
    held.bind(("127.0.0.1", spare))
    held.listen(8)
    try:
        assert not moabile.port_free(spare), spare
        assert moabile.port_listening(spare), spare
    finally:
        held.close()
    assert moabile.port_free(spare), "asking left the port bound"
    # And the wait uses the one that connects. port_free is still what picks
    # the port, so a couple of calls are its own; thirty are the wait loop.
    bound: list[int] = []
    was_free = moabile.port_free

    def record_free(port: int) -> bool:
        bound.append(port)
        return was_free(port)

    moabile.port_free = record_free
    try:
        await ios.drop_tunnel()
        assert await ios.tunnel_up(), log_text(ios)
    finally:
        moabile.port_free = was_free
    assert len(bound) <= 2, \
        f"port_free asked {len(bound)} times: either the wait loop binds again," \
        " or the port this panel wanted was taken and it had to scan"
    print("PASS the wait for the tunnel does not take the port away from iproxy")

    # u, or a panel closing, takes the tunnel away while it is still coming up:
    # what waited on it must give up quietly rather than reach for a process
    # that is gone, or blame the phone for a terminate of ours.
    await ios.drop_tunnel()
    coming = asyncio.create_task(ios.tunnel_up())
    await asyncio.sleep(0.2)                 # inside its first wait
    await ios.drop_tunnel()
    assert await coming is False, "a tunnel taken away while opening was called up anyway"
    assert "tunnel-down" not in ios._said, \
        "our own drop_tunnel was reported as the phone's fault"
    print("PASS a tunnel taken away while it opens is given up on, not blamed on the phone")


async def phase_ios_login(app, pilot) -> None:
    """the ssh account: which one, what it can reach, and what sudo covers.

    Split from phase_ios, which had grown past six hundred lines: this half
    starts from the panel rather than from wherever the half above left the
    screen, and it is the only one that touches the login.
    """
    ios = app.panel(IOS_UDID)

    # Whatever the phases above left on screen, the login tests start from
    # the panel: a modal still up would eat every key they press.
    for _ in range(4):
        if app.screen is app.screen_stack[0]:
            break
        await pilot.press("escape")
        await pilot.pause(0.1)
    assert app.screen is app.screen_stack[0], app.screen

    ios.focus()
    await pilot.pause()

    async def login_as(user: str) -> None:
        """Drive u: which account, host and port this phone is reached with."""
        await pilot.press("u")
        assert await on_screen(pilot, app, moabile.AskScreen), app.screen
        app.screen.query_one("#answer", Input).value = f"{user}@127.0.0.1:{ios.ssh_port}"
        await pilot.press("enter")

    try:
        # Anything the poll has already said about the old login is not an
        # answer about the new one: u is the change made to fix it, and
        # whether it worked has to reach the screen rather than being held
        # back as something said once already.
        ios.say_once("stats", "stats unavailable: something about the old login")
        assert "stats" in ios._said, ios._said
        await login_as("root")                   # u really changes the account…
        assert ios.ssh_user == "root", ios.ssh_user
        assert "stats" not in ios._said, ios._said
        await login_as("mobile")                 # …and back, which is the default
        assert (ios.ssh_user, ios.ssh_host) == ("mobile", "127.0.0.1"), ios.ssh_user
        assert await settle(pilot, lambda: ios.packages and app.screen is app.screen_stack[0],
                            tries=400), (ios.packages, app.screen)
        # The default every jailbreak ships with is what it starts from, and it
        # never reaches a command line for ps to show or a file on disk.
        assert ios.password == "alpine", ios.password
        # Keys are never offered on the connection that authenticates: sshd
        # counts each one as a failed try and drops the connection before it
        # ever asks for a password.
        auth = ios.ssh_argv("-M", "-N", batch=False)
        assert "PubkeyAuthentication=no" in auth, auth
        # ControlPersist would fork the master into the background the instant it
        # authenticated, exiting the process open_master watches — which it could
        # only report as a refused password, once per panel opened.
        assert "ControlPersist=no" in auth and "ControlPersist=30" not in auth, auth
        # The prompt is not always the literal "password:": keyboard-interactive
        # puts the account in the middle of it.
        for shape in ("root@host's password: ",
                      "(mobile@localhost) Password for mobile@some-iPhone: ",
                      "Password:"):
            assert re.search(moabile.SSH_PROMPT, shape, re.IGNORECASE), shape
        assert not re.search(moabile.SSH_PROMPT,
                              "Permission denied (publickey,password).", re.IGNORECASE)
        assert "PreferredAuthentications=keyboard-interactive,password" in auth, auth
        assert "BatchMode=yes" not in auth, auth
        assert "BatchMode=yes" in ios.ssh_argv("id"), ios.ssh_argv("id")
        assert "alpine" not in (TMP / "ssh-log").read_text(), "the password reached a command line"
        # A non-interactive ssh has neither /usr/sbin nor anything a rootless
        # jailbreak keeps under /var/jb on its PATH, so every command carries
        # the export — and sudo replaces the PATH it is handed with its own
        # secure_path, so it is inside the quoting as well as outside it.
        (TMP / "ssh-log").write_text("")
        await ios.run("id", root=False)
        assert "export PATH=" in (TMP / "ssh-log").read_text(), (TMP / "ssh-log").read_text()
        (TMP / "ssh-log").write_text("")
        await ios.run("id")
        sudoed = (TMP / "ssh-log").read_text()
        assert sudoed.count("export PATH=") == 2, sudoed
        print("PASS every command carries the PATH a rootless jailbreak needs")
        assert not list(Path(TMP).glob("*.json")), "a state file is back"
        # Nothing of ours goes onto the phone to make this work: no key, no agent.
        assert "ssh-copy-id" not in Path(moabile.__file__).read_text(), "a key is being installed"
        print("PASS the login is a password, never a key left on the phone")

        # Holding the lock is what the app does around opening a connection,
        # and what keeps a login still settling in the background from
        # opening one underneath these checks.
        async with ios.master_lock:
            # The connection that carries everything else: opened on a pty of its
            # own, and only adopted once it is really up. A refused ssh sits there
            # re-prompting, alive and carrying nothing.
            (TMP / "ios-pw-changed").touch()
            ios.drop_master()
            (TMP / "ssh-master").unlink(missing_ok=True)
            assert await ios.open_master("alpine") != "", "a refused password reported a connection"
            assert ios.master is None, "a refused ssh was kept as the master"
            assert await ios.open_master("not-alpine") == "", log_text(ios)
            assert ios.master is not None and ios.master.poll() is None, ios.master
            print("PASS the master is opened with a password and adopted only once it is up")

            # ssh leaves its control socket behind when it is killed rather than
            # asked to close, and -M will not reuse one it finds — so a socket
            # an older run left there had every open asking for a password.
            ios.drop_master()
            (TMP / "ssh-master").unlink(missing_ok=True)
            Path(ios.control_path()).write_text("a socket an earlier run left")
            assert await ios.open_master("not-alpine") == "", log_text(ios)
            assert ios.master is not None and ios.master.poll() is None, ios.master
            print("PASS a control socket left behind is cleared, not asked around")

            # The password is typed when ssh stops echoing, not when the question
            # appears: the terminal switch that comes with the question throws away
            # anything already typed, which is how a correct password went nowhere.
            # Where that switch cannot be read back, the prompt itself is the cue.
            (TMP / "ios-echo-on").touch()
            ios.drop_master()
            (TMP / "ssh-master").unlink(missing_ok=True)
            assert await ios.open_master("not-alpine") == "", log_text(ios)
            (TMP / "ios-echo-on").unlink()
            print("PASS the prompt is answered on the echo going off, or a beat after it shows")

            # And on that path the terminal is still echoing, so the password
            # comes straight back down the pty as input — which is the one
            # thing in here that must not reach the panel log or an svg of the
            # screen. A refusal that says nothing after it used to leave the
            # password as the last line, which is exactly what gets reported.
            (TMP / "ios-echo-on").touch()
            (TMP / "ios-quiet-refusal").touch()
            ios.drop_master()
            (TMP / "ssh-master").unlink(missing_ok=True)
            Path(ios.control_path()).unlink(missing_ok=True)
            # The wrong one, since this phone's is not-alpine by now: only a
            # refusal reports anything at all.
            refusal = await ios.open_master("alpine")
            assert refusal and "alpine" not in refusal, refusal
            assert "alpine" not in log_text(ios), log_text(ios)
            (TMP / "ios-quiet-refusal").unlink()
            (TMP / "ios-echo-on").unlink()
            print("PASS the password is never in what ssh is reported to have said")

        # Wrong default: asked once, masked, and kept in memory rather than saved.
        ios.drop_master()
        ios.password, ios.master_said = "alpine", False
        await pilot.press("i")               # any device command wants the connection
        assert await on_screen(pilot, app, moabile.AskScreen, tries=400), \
            app.screen
        assert "password for" in app.screen.title_text, app.screen.title_text
        assert app.screen.query_one("#answer", Input).password is True, "the password was shown"
        app.screen.query_one("#answer", Input).value = "not-alpine"
        await pilot.press("enter")
        assert await settle(pilot, lambda: ios.password == "not-alpine", tries=400), ios.password
        assert await settle(pilot, lambda: ios.master is not None
                            and ios.master.poll() is None, tries=400), ios.master
        assert not list(Path(TMP).glob("*.json")), "a state file is back"
        print("PASS a password the default does not open is asked for, masked, and never stored")

        # Refused once is refused until something asks again: the connection is
        # wanted every three seconds, and a prompt that often is unusable.
        ios.drop_master()
        ios.master_said = True
        rc, out = await ios.run("id")
        assert rc != 0 and "no ssh connection" in out, (rc, out)
        assert app.screen is app.screen_stack[0], "it asked again on the next command"
        ios.master_said = False
        assert await ios.open_master(ios.password) == "", log_text(ios)
        print("PASS a refused password is not asked for again on every command")
    finally:
        # Back to a phone with the default password, and a connection that will
        # open with it, for everything after this.
        (TMP / "ios-pw-changed").unlink(missing_ok=True)
        ios.drop_master()
        ios.password, ios.master_said = "alpine", False

    # Root as mobile is sudo, the way root as shell on android is su.
    (TMP / "ssh-log").write_text("")
    await ios.describe()
    assert ios.root is True, log_text(ios)
    assert "sudo -S -p" in (TMP / "ssh-log").read_text(), (TMP / "ssh-log").read_text()
    (TMP / "ios-nosudo").touch()
    await ios.describe()
    assert ios.root is False, "a phone with no sudo reported root"
    (TMP / "ios-nosudo").unlink()
    print("PASS as a non-root login every command goes through sudo")

    # scp runs as the login user, so it cannot write where frida-server goes:
    # the file lands where mobile can put it and sudo moves it into place.
    (TMP / "scp-staged").write_text("")
    (TMP / "ios-edits").write_text("")
    rc, out = await ios.push("/tmp/some-frida-server", ios.server_path)
    assert rc == 0, out
    assert "/var/mobile/some-frida-server" in (TMP / "scp-staged").read_text(), \
        (TMP / "scp-staged").read_text()
    assert "mv /var/mobile/some-frida-server /usr/sbin/frida-server" \
        in (TMP / "ios-edits").read_text(), (TMP / "ios-edits").read_text()
    print("PASS a push scp cannot make as mobile is staged and moved as root")

    # The host is whatever was typed at u, and an IPv6 literal is written in
    # brackets — which the stats line, being markup, reads as a style it cannot
    # resolve. It is a row on the screen, so it has to arrive escaped.
    (TMP / "ios-noip").touch()
    was_host = ios.ssh_host
    for host in ("[fe80::1%en0]", "[/]"):
        ios.ssh_host = host
        await ios.refresh_stats()
        await pilot.pause()
        assert host in _stats(ios), (host, _stats(ios))
    ios.ssh_host = was_host
    (TMP / "ios-noip").unlink()
    print("PASS an address the panel was pointed at is a row, not markup")

    ios.ssh_user = moabile.IOS_DEFAULT_USER       # back to the rest of the suite

    await ios.drop_tunnel()
    app._ticking = False

    # Client and server have to be the same version, and the error frida
    # prints for a mismatch names neither number.
    (TMP / "ios-frida").touch()
    (TMP / "ios-frida-version").write_text("16.0.1")
    await ios.ensure_frida()
    assert await settle(pilot, lambda: "16.0.1 on the device" in log_text(ios)), log_text(ios)
    (TMP / "ios-frida-version").unlink()
    (TMP / "ios-frida").unlink(missing_ok=True)
    print("PASS a frida-server that does not match the client is called out")

    # p takes the agent with the server: frida-server loads it from beside
    # itself, so one without the other is dead weight on the phone.
    junk = ios.server_junk
    assert junk.endswith("/usr/lib/frida"), junk
    (TMP / "ios-edits").write_text("")
    await pilot.press("p")
    await confirm(pilot, app, "y")
    # On the edits file, not the log: "removed" is already in there from the
    # browser, and a wait that is satisfied before the work starts proves none.
    assert await settle(pilot, lambda: "rm -rf" in (TMP / "ios-edits").read_text(),
                        tries=300), (TMP / "ios-edits").read_text()
    edits = (TMP / "ios-edits").read_text()
    assert "/usr/sbin/frida-server" in edits and "/usr/lib/frida" in edits, edits
    print("PASS p takes the frida agent off the phone with the server")

    tunnel = ios.tunnel
    await app.toggle_panel(IOS_UDID)             # close the panel
    assert tunnel is not None and tunnel.returncode is not None, "the tunnel outlived its panel"
    (TMP / "ios").unlink()
    await app.refresh_devices()
    assert IOS_UDID not in app.serials, app.serials
    assert len(app.panels) == 2, app.panels
    print("PASS closing an ios panel takes its iproxy tunnel with it")


async def phase_teardown(app, pilot) -> None:
    """what happens when panels and devices go away."""

    # With no panel open every key used to do nothing at all, silently.
    notes: list[str] = []
    app.notify = lambda message, **_kw: notes.append(message)
    for serial in list(app.serials):
        if app.panel(serial):
            await app.toggle_panel(serial)
    assert not app.panels, app.panels
    assert app.query_one("#empty").display, "no hint where the panels used to be"
    assert app.sub_title == "no device", app.sub_title
    # Focus can still be sitting in the sidebar filter, which would eat every
    # letter before it ever reached a binding.
    app.set_focus(None)
    await pilot.pause(0.3)
    notes.clear()
    for key in ("f", "s", "o", "w", "t", "l", "d", "i", "k"):
        await pilot.press(key)
    await pilot.pause()
    # any, not all: work left over from the frida phase reports itself here too.
    assert any("no device panel" in note for note in notes), notes
    assert len([n for n in notes if "no device panel" in n]) == 9, notes
    print("PASS actions explain themselves when no panel is open")

    # And b with no panel to hand the keyboard to: the sidebar goes invisible,
    # so it must not keep it — enter and the arrows would be going to a list of
    # rows nobody can see. It only ever handed focus over where a panel existed.
    app.query_one("#devices", ListView).focus()
    await pilot.pause()
    await pilot.press("b")
    await pilot.pause()
    assert app.query_one("#side").display is False, "b did not hide the sidebar"
    assert app.focused is None, app.focused
    notes.clear()
    await pilot.press("i")                   # and the keys still reach the app
    await pilot.pause()
    assert any("no device panel" in note for note in notes), notes
    await pilot.press("b")                   # back again, for what comes after
    await pilot.pause()
    assert app.query_one("#side").display is True, "b did not bring the sidebar back"
    print("PASS b hiding the sidebar does not leave the keyboard inside it")

    # Unplugging has to take the panel and everything it started with it.
    await app.toggle_panel("emulator-5556")
    panel = app.panel("emulator-5556")
    panel.start_stream("logcat", "adb", "-s", "emulator-5556", "logcat")
    assert await settle(pilot, lambda: "logcat" in panel.streams), panel.streams
    (TMP / "unplugged").touch()
    await app.refresh_devices()
    assert await settle(pilot, lambda: app.panel("emulator-5556") is None), app.serials
    assert not panel.streams, "a stream outlived the device it was reading"
    assert app.serials == ["emulator-5554"], app.serials
    print("PASS unplugging a device closes its panel and its streams")

    # Nothing attached at all: the middle of the screen and the title bar have
    # to say so, rather than leaving an empty box and a bare name.
    (TMP / "gone").touch()
    await app.refresh_devices()
    assert await settle(pilot, lambda: app.serials == []), app.serials
    assert app.sub_title == "no device", app.sub_title
    assert "no device attached" in str(app.query_one("#empty").render()), \
        str(app.query_one("#empty").render())
    assert "no panel" in str(app.query_one("#pkghead").render()), \
        str(app.query_one("#pkghead").render())
    (TMP / "gone").unlink()
    print("PASS with no device attached the screen says so, not nothing")

    # Attached but not usable: adb calls it unauthorized, and dropping it
    # silently is how "nothing attached" ends up on screen with a cable in.
    (TMP / "locked").touch()
    await app.refresh_devices()
    assert await settle(pilot, lambda: app.waiting == [("emulator-5554", "unauthorized")]), \
        app.waiting
    assert app.serials == [], app.serials
    middle = str(app.query_one("#empty").render())
    assert "unauthorized" in middle and "prompt" in middle, middle
    rows = app.query_one("#devices", ListView)
    assert [str(node.query_one(Label).render()) for node in rows._nodes] == \
        ["✗ emulator-5554  unauthorized"], [str(n.query_one(Label).render()) for n in rows._nodes]
    notes.clear()
    await app.toggle_panel("emulator-5554")
    assert not app.panels, "a panel opened on an unauthorized device"
    assert notes and "unauthorized" in notes[-1], notes
    (TMP / "locked").unlink()
    await app.refresh_devices()
    assert await settle(pilot, lambda: app.serials == ["emulator-5554"]), app.serials
    # adb's own chatter is not a device. The fake prints the header twice, the
    # way a cold daemon does with its two startup lines, and those used to come
    # back as a device called "List" that was "of".
    assert app.waiting == [], app.waiting
    print("PASS an unauthorized device is listed and explained, not hidden")

    # A panel that goes away must not keep the keyboard: every key would go to
    # a widget that is no longer on screen, and the app would look dead.
    assert app.focused is None or app.focused in app.screen.query("*"), app.focused

    # q is next to every other key, and a panel can be holding a frida session:
    # it asks, and only the yes actually leaves.
    exited: list[object] = []
    app.exit = lambda *a, **kw: exited.append(a)
    await pilot.press("q")
    await confirm(pilot, app, "n")
    await pilot.pause(0.3)
    assert not exited, "no kept the app open, but it quit anyway"
    await pilot.press("q")
    assert await on_screen(pilot, app, moabile.ConfirmScreen), app.screen
    await pilot.press("escape")              # escape is the same as no
    await pilot.pause(0.3)
    assert not exited, "escape quit the app"
    await pilot.press("ctrl+q")              # Textual's own quit key, same path
    assert await on_screen(pilot, app, moabile.ConfirmScreen), app.screen
    await pilot.press("n")
    await pilot.pause(0.3)
    assert not exited, "ctrl+q skipped the question"
    await pilot.press("q")
    await confirm(pilot, app, "y")
    assert await settle(pilot, lambda: bool(exited)), "y did not quit"
    print("PASS quitting asks first, and only yes leaves")


async def phase_edge_cases(app, pilot) -> None:
    """Exercise remaining UI action branches and error notifications."""
    panel = app.panels[0]
    fs = moabile.FilesScreen(panel)
    app.push_screen(fs)
    assert await on_screen(pilot, app, moabile.FilesScreen)
    fs.action_focus_host()
    fs.action_focus_device()
    fs.action_up()
    old_pkg = panel.package
    panel.package = ""
    fs.action_app_dir()
    panel.package = old_pkg
    fs.dismiss(None)
    await settle(pilot, lambda: type(app.screen) is not moabile.FilesScreen)

    old_tool = panel.mirror_tool
    panel.mirror_tool = "nonexistent_mirror_tool_xyz"
    app.action_mirror()
    panel.mirror_tool = old_tool


async def main() -> None:
    # A helper named run() would shadow App.run() and the TUI would never start.
    assert moabile.MOABile.run is App.run, "MOABile.run shadows Textual's App.run"

    assert await moabile._nothing() == (0, "")
    assert moabile.ios_memory([]) == "?"
    assert moabile.ios_memory(["hw.memsize 8589934592", "page size of 16384",
                               "Pages free: 100000", "Pages inactive: 50000",
                               "Pages speculative: 50000"]) != "?"
    assert moabile.mac_key("0:a:b:c:d:e") == "00:0a:0b:0c:0d:0e"
    assert moabile.mac_key("00-0A-0B-0C-0D-0E") == "00:0a:0b:0c:0d:0e"
    assert moabile.pid_of([], "Target") is None
    assert moabile.pid_of([" 1234 /Applications/Target.app/Target"], "Target") == "1234"
    assert moabile.pid_of([" 1234 /Applications/TargetHelper.app/TargetHelper"], "Target") is None
    assert moabile.pid_of([" 1234 /Applications/Target.app/Target"], "") is None
    # Apps sharing the same executable name (e.g. AppStable, App-Beta, AppAlpha)
    ps_shared = [
        " 1001 /private/var/containers/Bundle/Application/UUID-STABLE/AppStable.app/AppExecutable",
        " 2002 /private/var/containers/Bundle/Application/UUID-BETA/App-Beta.app/AppExecutable",
        " 3003 /private/var/containers/Bundle/Application/UUID-ALPHA/AppAlpha.app/AppExecutable",
    ]
    b_stable = "/var/containers/Bundle/Application/UUID-STABLE/AppStable.app"
    b_beta = "/var/containers/Bundle/Application/UUID-BETA/App-Beta.app"
    b_alpha = "/var/containers/Bundle/Application/UUID-ALPHA/AppAlpha.app"
    assert moabile.pid_of(ps_shared, "AppExecutable", b_stable) == "1001"
    assert moabile.pid_of(ps_shared, "AppExecutable", b_beta) == "2002"
    assert moabile.pid_of(ps_shared, "AppExecutable", b_alpha) == "3003"
    assert moabile.pid_of([ps_shared[0], ps_shared[2]], "AppExecutable", b_beta) is None
    assert moabile.pid_of([ps_shared[1]], "AppExecutable", b_stable) is None
    assert moabile.last_line("") == ""
    assert moabile.last_line("  first\n  second  \n\n") == "second"
    assert moabile.not_there("sh: open: not found") is True
    assert moabile.not_there("No such file or directory") is True
    assert moabile.not_there("Success") is False
    assert moabile.first({"sec": ["foo 123 bar"]}, "sec", r"foo (\d+) bar") == "123"
    assert moabile.first({}, "sec") is None
    with patch.dict(moabile._HELP, {("ideviceinstaller", "--install"): True}):
        assert await moabile.installer_takes_commands() is False
        moabile._HELP[("ideviceinstaller", "--install")] = False
        assert await moabile.installer_takes_commands() is True

    parsed = moabile.sections("@batt\n  level: 87\n@load\n0.4 0.3\n@frida\n")
    assert parsed == {"batt": ["  level: 87"], "load": ["0.4 0.3"], "frida": []}, parsed
    assert moabile.sections("noise before any marker") == {}
    for text in ("", "@", "@@", "\r\n", "@" * 500, "@k\nv", "\x00@k\nv"):
        moabile.sections(text)
    for colour in ("", "default", "brown", "zzz", "ffffff", "GGGGGG", "[/]", "\x00"):
        moabile.pyte_color(colour)
    assert moabile.pyte_color("brown") == "yellow" and moabile.pyte_color("default") is None
    assert moabile.pyte_color("ff8800") == "#ff8800"
    # Real codeshare markup: slug out of the URL (not the display title),
    # likes out of the icon line, pager out of the ?page= links.
    real = article("Gand3lf", "xamarin-antiroot", "Xamarin AntiRoot", "11",
                   "Bypass antiroot detection for Xamarin apps! &quot;quoted&quot;")
    scripts, pages = moabile.parse_codeshare(real + f'<ul class="pagination">{PAGER}</ul>')
    assert pages == 4 and len(scripts) == 1, (pages, scripts)
    assert scripts[0].slug == "Gand3lf/xamarin-antiroot", scripts[0]
    assert scripts[0].title == "Xamarin AntiRoot" and scripts[0].likes == "11", scripts[0]
    assert scripts[0].about == 'Bypass antiroot detection for Xamarin apps! "quoted"', scripts[0]
    # A page of nothing, half an entry, or an owner page with no project must
    # come back empty rather than raise inside the worker.
    for junk in ("", "<article>", '<article><h2><a href="/@x/">t</a></h2>', "?page=x", "<p>x</p>"):
        assert moabile.parse_codeshare(junk) == ([], 1), junk
    # The same rule one step further in: what the device calls an app ends up
    # as a path on this machine, so an identifier that is a path is not one
    # this takes either. The dot is what the ios app list's header row fails.
    # One rule for shortening a serial, and the ends are what tell two udids
    # apart: a cut off the front drops the only characters that differ. An
    # android serial is short enough to come back whole.
    assert moabile.short_serial("emulator-5554") == "emulator-5554"
    short = moabile.short_serial(IOS_UDID)
    assert len(short) == 15 and short.startswith(IOS_UDID[:10]) \
        and short.endswith(IOS_UDID[-4:]), short
    for good in ("com.target.app", "com.example.app-1", "a.b"):
        assert moabile.is_package(good), good
    for bad in ("../../etc/passwd", "com.evil app", "CFBundleIdentifier", "",
                "com..evil", "/etc/passwd", "com.x/y", "com.x\ny"):
        assert not moabile.is_package(bad), bad
    # The slug ends up in frida's argument list, so a page that puts a space or
    # a flag in one is not a slug this takes: skipped, not passed on.
    hostile = '<article><h2><a href="/@evil/x -l /etc/shadow/">t</a></h2></article>'
    assert moabile.parse_codeshare(hostile) == ([], 1), moabile.parse_codeshare(hostile)
    # Nothing of the run is written anywhere but the frida-server cache, which
    # is a cache: regenerable, in the place caches go, and one version deep.
    assert not [p for p in Path(TMP).iterdir()
                if p.is_file() and p.suffix in (".json", ".conf", ".ini")], \
        list(Path(TMP).iterdir())
    # A binding naming an action that does not exist fails silently at runtime.
    for cls_screen in (moabile.MOABile, moabile.DepsScreen, moabile.FridaArgsScreen, moabile.ConfirmScreen,
                       moabile.FilesScreen, moabile.ScriptScreen, moabile.CodeshareScreen, moabile.TextViewerScreen):
        for binding in cls_screen.BINDINGS:
            if isinstance(binding, moabile.Binding):
                assert hasattr(cls_screen, f"action_{binding.action}"), (cls_screen.__name__, binding.action)
    app_bindings = [b for b in moabile.MOABile.BINDINGS if isinstance(b, moabile.Binding)]
    assert {b.key for b in app_bindings} == {
        "r", "b", "f", "s", "o", "w", "t", "l", "slash", "c", "alt+c", "f8", "d", "a", "e", "i", "u", "p", "k", "v",
        "m", "h", "q"}
    # A key that stands for nothing in the word beside it has to be memorised
    # twice, so the bar is built the other way round: the label is chosen to
    # start with its key. Three cannot — b for the sidebar's bar, v for svg, d
    # for files — and k for clear is the plain shell convention.
    off = [(b.key, b.description) for b in app_bindings
           if not b.description.startswith(b.key)]
    assert off == [
        ("b", "sidebar"), ("slash", "log filter"), ("alt+c", "copy terminal"),
        ("f8", "leave terminal"), ("d", "files"), ("k", "clear"), ("v", "svg"),
    ], off
    # The bar has room for a word each, so the whole sentence lives in the
    # tooltip — which is what hovering a key and the h panel show.
    assert all(b.tooltip for b in app_bindings), \
        [b.key for b in app_bindings if not b.tooltip]
    print("PASS every binding resolves to an action that exists")

    # The logo measures itself for viewport size checks.
    assert moabile.LOGO_ROWS == len(moabile.LOGO.splitlines()), moabile.LOGO_ROWS
    assert moabile.LOGO_COLS == max(len(ln) for ln in moabile.LOGO.splitlines())
    print("PASS the logo measures itself, and carries no markup that breaks it")

    # Every colour either theme writes with lands on one of three grounds, and
    # a status colour nobody can read is not a status. WCAG AA is 4.5:1, and a
    # hex nudged by hand is exactly how that gets lost.
    def channel(value: float) -> float:
        value /= 255
        return value / 12.92 if value <= 0.04045 else ((value + 0.055) / 1.055) ** 2.4

    def luminance(colour: str) -> float:
        r, g, b = (int(colour.lstrip("#")[i:i + 2], 16) for i in (0, 2, 4))
        return 0.2126 * channel(r) + 0.7152 * channel(g) + 0.0722 * channel(b)

    def contrast(one: str, two: str) -> float:
        top, bottom = sorted((luminance(one), luminance(two)), reverse=True)
        return (top + 0.05) / (bottom + 0.05)

    assert round(contrast("#ffffff", "#000000")) == 21, contrast("#ffffff", "#000000")
    for theme in (moabile.DARK, moabile.LIGHT):
        for role in ("foreground", "primary", "secondary", "accent",
                     "success", "warning", "error"):
            for ground in (theme.background, theme.surface, theme.panel):
                assert ground is not None
                ratio = contrast(getattr(theme, role), ground)
                assert ratio >= 4.5, (theme.name, role, ground, round(ratio, 2))
    print("PASS both themes clear 4.5:1 for every colour on every ground")

    # libusbmuxd 2.0 changed iproxy's argument order, so both shapes are
    # spelled out here: guessing wrong is a tunnel that never comes up.
    with patch.dict(moabile._HELP, {("iproxy", "--udid"): True}):
        assert await moabile.iproxy_argv(2222, "UDID") == ["iproxy", "2222:22", "-u", "UDID"]
        moabile._HELP[("iproxy", "--udid")] = False
        assert await moabile.iproxy_argv(2222, "UDID") == ["iproxy", "2222", "22", "UDID"]

    # A .deb is parsed here rather than shelled out to dpkg, so what is not one
    # has to come back as an error and not as half an unpacked tree.
    junk_deb = TMP / "notadeb.deb"
    junk_deb.write_bytes(b"nope, not an archive")
    for blob, why in ((b"nope, not an archive", "not a deb"),
                      (b"!<arch>\n" + f"{'control.tar':<16}{'0':<12}{'0':<6}{'0':<6}"
                       f"{'100644':<8}{'4':<10}".encode() + b"`\nhi\n\n", "no data archive")):
        junk_deb.write_bytes(blob)
        try:
            moabile.unpack_deb(junk_deb, TMP / "nowhere")
            raise AssertionError(f"{why}: unpacked anyway")
        except ValueError as exc:
            assert why in str(exc), exc
    assert not (TMP / "nowhere").exists(), "a refused deb left a tree behind"
    junk_deb.unlink()
    print("PASS iproxy's two argument shapes, and a .deb that is not one")

    # An archive off the internet does not get to choose where its files land,
    # and the filter that says so is newer than the python this asks for — so
    # the members are written by name here, and that is what has to hold.
    trap, into = TMP / "trap.deb", TMP / "trap-unpacked"
    inner = io.BytesIO()
    with tarfile.open(fileobj=inner, mode="w") as tar:
        for name, blob in (("../escaped", b"nope"), ("/absolute", b"nope"),
                           ("./var/jb/ok", b"fine")):
            info = tarfile.TarInfo(name)
            info.size = len(blob)
            tar.addfile(info, io.BytesIO(blob))
        link = tarfile.TarInfo("./var/jb/link")
        link.type, link.linkname = tarfile.SYMTYPE, "/etc/passwd"
        tar.addfile(link)
    trap.write_bytes(b"!<arch>\n" + ar_member("data.tar", inner.getvalue()))
    written = moabile.unpack_deb(trap, into)
    # In tar order, with the one that climbs out dropped and the absolute one
    # landed inside the tree rather than at its own name.
    assert written == ["/absolute", "/var/jb/ok"], written
    assert (into / "var/jb/ok").read_bytes() == b"fine", written
    assert not (TMP / "escaped").exists(), "a member climbed out of the tree"
    assert not (into / "var/jb/link").exists(), "a symlink was written"
    assert sorted(p.name for p in into.rglob("*") if p.is_file()) == ["absolute", "ok"], \
        sorted(str(p) for p in into.rglob("*"))
    shutil.rmtree(into, ignore_errors=True)
    trap.unlink()
    print("PASS a deb cannot write outside the directory it is unpacked into")

    # The command line is a door: --help and --version answer without painting
    # a screen, and an argument it has no use for is an error rather than a TUI
    # that leaves you wondering which of the two you got wrong.
    said_out = io.StringIO()
    with contextlib.redirect_stdout(said_out), contextlib.redirect_stderr(io.StringIO()):
        assert moabile.main(["--help"]) == 0 and moabile.main(["-V"]) == 0
        assert moabile.main(["--nope"]) == 2, "an unknown argument was swallowed"
        orig_argv = sys.argv
        try:
            sys.argv = ["moabile", "-V"]
            assert moabile.main() == 0, "main() without arguments should use sys.argv[1:]"
        finally:
            sys.argv = orig_argv
    assert "python3 moabile.py" in said_out.getvalue(), said_out.getvalue()
    assert moabile.VERSION in moabile.USAGE, moabile.USAGE
    print("PASS --help and --version answer, and a stray argument is an error")

    # Anything the three-second poll can say has to be said once and then held:
    # an unguarded write in one of these buries the panel's own record of the
    # work under the same line every few seconds, which is how "no address off
    # the phone" ended up in the log twenty times a minute.
    source = Path(moabile.__file__).read_text()
    lines = source.splitlines()
    polled = {("IosPanel", "stats"), ("IosPanel", "address"), ("IosPanel", "tunnel_up"),
              ("IosPanel", "master_up"), ("AndroidPanel", "stats"),
              ("DevicePanel", "refresh_stats"), ("DevicePanel", "say_stats")}
    seen = set()
    for ast_cls in [n for n in ast.parse(source).body if isinstance(n, ast.ClassDef)]:
        for fn in [n for n in ast_cls.body if isinstance(n, (ast.AsyncFunctionDef, ast.FunctionDef))]:
            if (ast_cls.name, fn.name) not in polled:
                continue
            seen.add((ast_cls.name, fn.name))
            body = "\n".join(lines[fn.lineno - 1:fn.end_lineno])
            if re.search(r"self\.(write|fail)\(", body):
                assert re.search(r"say_once|_said|_shown|_no_ip_tool", body), \
                    f"{ast_cls.name}.{fn.name} says something every poll with nothing holding it"
    assert seen == polled, f"a polled method was renamed: {polled - seen}"
    print("PASS nothing the status poll says can repeat itself")
    print("PASS pure helpers: the parsers, the colours, and nothing written to disk")

    # A device that goes away leaves adb blocked forever; with a poll every few
    # seconds those pile up until the interface stops responding.
    began = time.monotonic()
    rc, out = await moabile.sh("sleep", "30", timeout=0.4)
    assert rc == 124 and "timed out" in out, (rc, out)
    assert time.monotonic() - began < 5, "the timeout did not actually cut it short"
    # `sh -c "curl | xz -d"` used to leave curl running when the timeout fired.
    mark = "9" + "1731"          # built here so no ancestor's command line holds it
    rc, _ = await moabile.sh("sh", "-c", f"sleep {mark} | cat", timeout=0.4)
    assert rc == 124, rc
    await asyncio.sleep(0.3)
    _, out = await moabile.sh("pgrep", "-af", f"[s]leep {mark}")
    listing = out.splitlines()
    # Only the sleep itself counts: shells that merely quote the marker in their
    # own command line match too, which is the same trap as the frida-server one.
    survivors = [ln for ln in listing if ln.split(maxsplit=1)[1:] == [f"sleep {mark}"]]
    assert not survivors, f"the pipeline survived the timeout: {survivors}"
    print("PASS a hung command is killed with its whole process group")

    # No child of sh() gets the interface's stdin: ssh and adb both forward
    # theirs to the far end, so an inherited one reads the keys meant for the
    # app — every three seconds, once per status poll.
    rc, out = await moabile.sh("sh", "-c", "read -r line && echo GOT:$line || echo EOF",
                               timeout=5)
    assert (rc, out.strip()) == (0, "EOF"), (rc, out)
    # And the one that is fed still is: that is how sudo is told a password
    # without it ever appearing in an argument list.
    assert await moabile.sh("cat", feed=b"fed") == (0, "fed"), await moabile.sh("cat", feed=b"fed")
    print("PASS a command gets no stdin unless it is fed one")

    await test_gate()
    await test_vanishing()
    test_controlling_terminal()
    await test_logo_only_where_it_fits()
    await test_hostile_device()
    await test_stress()
    await test_edge_cases()

    app = moabile.MOABile()
    async with app.run_test() as pilot:
        assert await on_screen(pilot, app, moabile.DepsScreen)
        await pilot.press("enter")
        assert await settle(pilot, lambda: bool(app.panels), tries=200), app.panels
        assert app.serials == ["emulator-5554", "emulator-5556"], app.serials
        select(app.query_one("#devices", ListView), "emulator-5556")
        assert await settle(pilot, lambda: len(app.panels) == 2), app.panels
        # A panel is mounted before load() has finished reading the device, and
        # every phase below asserts on what that read found — so wait for the
        # read, not for the panel to merely exist.
        assert await settle(pilot, lambda: all(p.props and p.packages for p in app.panels),
                            tries=200), [(p.serial, bool(p.props)) for p in app.panels]

        # One app for all of them: booting it costs a second each time.
        # They run in this order, and each states what it expects to find.
        await phase_devices(app, pilot)
        await phase_sidebar_cost(app, pilot)
        await phase_keys(app, pilot)
        await phase_tools(app, pilot)
        await phase_scripts(app, pilot)
        await phase_apk(app, pilot)
        await phase_streams(app, pilot)
        await phase_files(app, pilot)
        await phase_resilience(app, pilot)
        await phase_frida_server(app, pilot)
        await phase_ios(app, pilot)
        await phase_ios_login(app, pilot)
        await phase_edge_cases(app, pilot)
        await phase_teardown(app, pilot)

    # Nothing the app started is still running now that it is gone. Every fake
    # carries this run's own directory in its command line and the tunnel holds
    # a real port, so a stray of either kind is a process that outlived the app
    # which spawned it — the one thing this program promises about the machine
    # it runs on, and the one thing no other check here looks at as a whole.
    # Nothing new where the suite was started from either. Everything it
    # writes belongs under its own temporary directory, and a test that points
    # a picker at nowhere in particular is how a checkout collects apks.
    left = sorted({p.name for p in STARTED_IN.iterdir()} - WAS_THERE)
    assert not [n for n in left if not n.startswith(".") and n != "__pycache__"], left

    strays: list[str] = []
    for _ in range(40):
        _, alive = await moabile.sh("pgrep", "-af", str(TMP))
        strays = [ln for ln in alive.splitlines() if ln.strip() and "pgrep" not in ln]
        if not strays and moabile.port_free(moabile.IOS_SSH_PORT):
            break
        await asyncio.sleep(0.1)
    assert not strays, strays
    assert moabile.port_free(moabile.IOS_SSH_PORT), "a usb tunnel outlived the app"
    print("PASS nothing the app started is left running when the app is gone")

asyncio.run(main())
# Only on the way out clean: a run that failed leaves its fake tools, logs and
# staged files where they can be looked at, and a run that passed leaves the
# machine as it found it — which is what the app under test claims for itself.
shutil.rmtree(TMP, ignore_errors=True)
print("all good")
