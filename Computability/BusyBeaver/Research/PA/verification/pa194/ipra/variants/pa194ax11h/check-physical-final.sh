#!/usr/bin/env bash
set -euo pipefail
ulimit -s unlimited
ulimit -c 0

controller=$(cd -- "${1:?checked AX11H controller stage required}" && pwd)
coverage=$(cd -- "${2:?checked AX11H coverage stage required}" && pwd)
out=${3:?fresh output directory required}
here=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
mkdir -p "$out"
out=$(cd -- "$out" && pwd)
export LEAN_PATH="$(python3 - "$out" "$controller" "$coverage" <<'PY'
from pathlib import Path
import sys

out, *stages = map(Path, sys.argv[1:])
paths = [str(p) for p in (out, *stages)]
for stage in stages:
    paths.extend((stage / 'leanpath.txt').read_text().strip().split(':'))
print(':'.join(dict.fromkeys(p for p in paths if p)))
PY
)"
mod=PA194AX11HPhysicalFinal
log="$out/$mod.log"
if ! lean -j1 -M5350 -R "$here" -o "$out/$mod.olean" "$here/$mod.lean" >"$log" 2>&1; then
  cat "$log"
  exit 1
fi
cat "$log"
rg -Fxq "'$mod.halt_iff_site10' depends on axioms: [propext, Classical.choice, Quot.sound]" "$log"
printf '%s\n' "$LEAN_PATH" >"$out/leanpath.txt"
