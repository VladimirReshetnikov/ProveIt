#!/bin/sh
# Serialized single-module Lean build driver.
#
# Usage: build_one.sh <Module> [<Module> ...]
#   Builds FabiusFunction.<Module> one at a time, in order, each only after
#   no lean.exe is running anywhere on the machine (another agent session may
#   hold the kernel).  Exactly one lean process at a time; LAKE_JOBS=1.
#
# READ YOUR OWN LOG.  Each run writes its full output to a private
#   Analysis/FabiusFunction/scripts/build_one.<pid>.log
# whose path is printed on stdout as the first line, and appends only its
# summary lines to the shared Analysis/FabiusFunction/scripts/build_one.log.
#
# This split exists because the shared log used to be truncated at startup and
# read by everyone.  With more than one agent session on the machine that is
# safe for mutual exclusion but NOT for attribution: a second driver starting
# after the first one died would truncate the log, and a reader polling it
# would take the newcomer's BUILD-FINISHED and ALL-DONE for its own.  That
# happened.  The shared log is therefore append-only now, every line carries
# driver=<pid>, and it is trimmed rather than truncated; but a reader that
# wants to know how ITS build went should read the private log.
#
# Each module ends with
#   BUILD-FINISHED <Module> EXIT=<code> (<seconds>s) driver=<pid>
# and the whole run ends with ALL-DONE driver=<pid>.  The pid is appended, not
# prefixed, so existing greps keep matching.
#
# A PID lock refuses to start while a previous driver is alive, because
# stopping a harness task does not kill the script it launched.

set -u
HERE=$(cd "$(dirname "$0")" && pwd)
ROOT=$(cd "$HERE/../../.." && pwd)
LOG="$HERE/build_one.$$.log"
SHARED="$HERE/build_one.log"
LOCK="$HERE/build_one.pid"

if [ -f "$LOCK" ]; then
  old=$(cat "$LOCK" 2>/dev/null || echo 0)
  if [ "$old" != 0 ] && kill -0 "$old" 2>/dev/null; then
    echo "build_one.sh: another driver (pid $old) is still running; refusing to start" >&2
    exit 3
  fi
fi
echo $$ > "$LOCK"
trap 'rm -f "$LOCK"' EXIT INT TERM

: > "$LOG"
echo "$LOG"

# keep the shared log bounded without ever truncating another driver's tail
if [ -f "$SHARED" ]; then
  tail -n 2000 "$SHARED" > "$SHARED.trim" 2>/dev/null && mv "$SHARED.trim" "$SHARED"
fi

note() {
  echo "$1" >> "$LOG"
  echo "$1 driver=$$" >> "$SHARED"
}

cd "$ROOT" || exit 2

for mod in "$@"; do
  # wait (bounded) for a free kernel
  waited=0
  while tasklist 2>/dev/null | grep -qi "lean.exe"; do
    if [ "$waited" -ge 7200 ]; then
      note "WAIT-TIMEOUT $mod after ${waited}s; building anyway"
      break
    fi
    sleep 20
    waited=$((waited + 20))
  done
  note "BUILD-START $mod (waited ${waited}s) $(date +%H:%M:%S)"
  start=$(date +%s)
  LAKE_JOBS=1 lake build "+FabiusFunction.$mod" >> "$LOG" 2>&1
  code=$?
  end=$(date +%s)
  note "BUILD-FINISHED $mod EXIT=$code ($((end - start))s)"
  if [ "$code" != 0 ]; then
    cp "$LOG" "$HERE/build_one.last-fail.$$.log" 2>/dev/null
  fi
done
note "ALL-DONE"
