#!/bin/sh
# Serial validation of a change set and everything downstream of it.
#
# Usage:
#   Analysis/FabiusFunction/scripts/affected_modules.py <base> --out affected.txt
#   Analysis/FabiusFunction/scripts/validate_affected.sh affected.txt [logfile]
#
# One `lake` invocation per module, in the dependency order the companion
# script emits, so every dependency is already compiled by the time its
# consumer's turn comes and Lake has nothing to fan out over.  That is the
# whole point: a single umbrella invocation sizes its worker pool to hardware
# concurrency and has repeatedly exhausted this machine's memory.  See the
# caution at the top of Analysis/FabiusFunction/AGENTS.md.
#
# The log carries one line per module -- BUILT with a duration, `cached` when
# Lake had nothing to do, or FAIL with the first few error lines -- and ends
# with `VALIDATE-DONE modules=N failures=M`.  Read the log rather than the exit
# code of any single invocation.
#
# Failures reading an `.olean` (including `.olean.private`, and including the
# toolchain's own files) are out-of-memory symptoms rather than defects.  Do
# not edit Lean sources in response; rerun when the machine is quiet.

set -u

LIST=${1:?usage: validate_affected.sh <module-list> [logfile]}
ROOT=$(cd "$(dirname "$0")/../../.." && pwd)
LOG=${2:-"$ROOT/validate_affected.log"}

export LAKE_JOBS=1   # documented to be a no-op here; set anyway, relied on never

: > "$LOG"
total=$(grep -c . "$LIST")
i=0
fail=0

while IFS= read -r m; do
  m=$(printf '%s' "$m" | tr -d '\r')
  [ -z "$m" ] && continue
  i=$((i + 1))
  start=$(date +%s)
  out=$(cd "$ROOT" && lake build "+FabiusFunction.$m" 2>&1)
  rc=$?
  end=$(date +%s)
  if [ "$rc" -ne 0 ]; then
    fail=$((fail + 1))
    printf 'FAIL %s (%ss) [%s/%s]\n' "$m" "$((end - start))" "$i" "$total" >> "$LOG"
    printf '%s\n' "$out" | grep -E '^error' | head -5 >> "$LOG"
  elif printf '%s' "$out" | grep -q 'Built FabiusFunction'; then
    printf 'BUILT %s (%ss) [%s/%s]\n' "$m" "$((end - start))" "$i" "$total" >> "$LOG"
  else
    printf 'cached %s [%s/%s]\n' "$m" "$i" "$total" >> "$LOG"
  fi
done < "$LIST"

printf 'VALIDATE-DONE modules=%s failures=%s\n' "$i" "$fail" >> "$LOG"
[ "$fail" -eq 0 ]
