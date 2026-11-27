#!/usr/bin/env bash
set -euo pipefail
ulimit -s unlimited
ulimit -c 0

native=$(cd -- "${1:?checked LC_AX11H conditional endpoint required}" && pwd)
coverage=$(cd -- "${2:?checked LC_AX11H coverage required}" && pwd)
out=${3:?fresh output directory required}
here=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
test ! -e "$out"
mkdir -p "$out"
out=$(cd -- "$out" && pwd)

export LEAN_PATH="$(python3 -I - "$out" "$native" "$coverage" <<'PY'
from pathlib import Path
import sys

out, *stages = sys.argv[1:]
paths = [out, *stages]
for stage in stages:
    paths.extend((Path(stage) / 'leanpath.txt').read_text().strip().split(':'))
print(':'.join(dict.fromkeys(p for p in paths if p)))
PY
)"
module=PA194LCAX11HFinal
log="$out/$module.log"
if ! lean -j1 -M5500 -R "$here" -o "$out/$module.olean" "$here/$module.lean" >"$log" 2>&1; then
  cat "$log"
  exit 1
fi
cat "$log"
tr -s '[:space:]' ' ' <"$log" |
  rg -Fq "'$module.consistency_iff_literal_nonhalt' depends on axioms: [propext, Classical.choice, Quot.sound]"
printf '%s\n' "$LEAN_PATH" >"$out/leanpath.txt"
