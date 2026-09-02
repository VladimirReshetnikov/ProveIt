#!/bin/sh
# Serialized single-module Lean build driver.
#
# Usage: build_one.sh <Module> [<Module> ...]
#   Builds FabiusFunction.<Module> one at a time, in order, each only after
#   no lean.exe is running anywhere on the machine (another agent session may
#   hold the kernel).  Exactly one lean process at a time; LAKE_JOBS=1.
#
# Log: Analysis/FabiusFunction/scripts/build_one.log (truncated at start,
# so a queued run never shows stale output).  Each module ends with a line
#   BUILD-FINISHED <Module> EXIT=<code> (<seconds>s)
# and the whole run ends with ALL-DONE.
#
# A PID lock refuses to start while a previous driver is alive, because
# stopping a harness task does not kill the script it launched.

set -u
HERE=$(cd "$(dirname "$0")" && pwd)
ROOT=$(cd "$HERE/../../.." && pwd)
LOG="$HERE/build_one.log"
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
cd "$ROOT" || exit 2

for mod in "$@"; do
  # wait (bounded) for a free kernel
  waited=0
  while tasklist 2>/dev/null | grep -qi "lean.exe"; do
    if [ "$waited" -ge 7200 ]; then
      echo "WAIT-TIMEOUT $mod after ${waited}s; building anyway" >> "$LOG"
      break
    fi
    sleep 20
    waited=$((waited + 20))
  done
  echo "BUILD-START $mod (waited ${waited}s) $(date +%H:%M:%S)" >> "$LOG"
  start=$(date +%s)
  LAKE_JOBS=1 lake build "+FabiusFunction.$mod" >> "$LOG" 2>&1
  code=$?
  end=$(date +%s)
  echo "BUILD-FINISHED $mod EXIT=$code ($((end - start))s)" >> "$LOG"
  if [ "$code" != 0 ]; then
    cp "$LOG" "$HERE/build_one.last-fail.log" 2>/dev/null
  fi
done
echo "ALL-DONE" >> "$LOG"
