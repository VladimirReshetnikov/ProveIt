#!/usr/bin/env bash
set -euo pipefail
ulimit -s unlimited
ulimit -c 0

command=$(cd -- "${1:?checked M5 command stage required}" && pwd)
paused=$(cd -- "${2:?checked paused primary field stage required}" && pwd)
out=${3:?fresh output directory required}
here=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
test ! -e "$out"
mkdir -p "$out"
out=$(cd -- "$out" && pwd)

export LEAN_PATH="$(python3 -I - "$out" "$command" "$paused" <<'PY'
from pathlib import Path
import sys

out, *stages = sys.argv[1:]
paths = [out, *stages]
for stage in stages:
    paths.extend((Path(stage) / 'leanpath.txt').read_text().strip().split(':'))
print(':'.join(dict.fromkeys(p for p in paths if p)))
PY
)"
modules=(PA194M5FetchAgree PA194M5FetchRestore PA194M5FetchPrefix PA194M5FetchReader
  PA194M5FetchDecode PA194M5FetchScheduler PA194M5DecodeScheduler PA194M5MPDispatch
  PA194M5MPArithmetic PA194M5GenericMPScheduler PA194M5MPFrame PA194M5MPFrameScheduler)
sources=()
for module in "${modules[@]}"; do
  source="$here/$module.lean"
  log="$out/$module.log"
  sources+=("$source")
  if ! lean -j1 -M5000 -R "$here" -o "$out/$module.olean" "$source" >"$log" 2>&1; then
    cat "$log"
    exit 1
  fi
  cat "$log"
  if rg -q "error[:(]|sorryAx|Lean.ofReduceBool|declaration uses 'sorry'" "$log"; then exit 1; fi
done
for theorem in PA194M5DecodeScheduler.fetchDecode PA194M5GenericMPScheduler.nextFields \
    PA194M5MPFrameScheduler.advance; do
  module=${theorem%%.*}
  tr -s '[:space:]' ' ' <"$out/$module.log" |
    rg -Fq "'$theorem' depends on axioms: [propext, Classical.choice, Quot.sound]"
done
sha256sum "${sources[@]}" "$here/check.sh" "$out"/*.olean >"$out/sha256.txt"
printf '%s\n' "$LEAN_PATH" >"$out/leanpath.txt"
