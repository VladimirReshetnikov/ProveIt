#!/usr/bin/env bash
set -euo pipefail
ulimit -s unlimited
ulimit -c 0

core=$(cd -- "${1:?checked scheduler core required}" && pwd)
fetch=$(cd -- "${2:?checked fetch and scheduler-frame stage required}" && pwd)
out=${3:?fresh output directory required}
here=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
mkdir -p "$out"
out=$(cd -- "$out" && pwd)
export LEAN_PATH="$(python3 - "$out" "$core" "$fetch" <<'PY'
from pathlib import Path
import sys

out, *stages = map(Path, sys.argv[1:])
paths = [str(p) for p in (out, *stages)]
for stage in stages:
    paths.extend((stage / 'leanpath.txt').read_text().strip().split(':'))
print(':'.join(dict.fromkeys(p for p in paths if p)))
PY
)"
for suffix in CacheFlag CacheInput HaltCommand HaltFrame; do
  mod=PA194AX11H$suffix
  lean -j1 -M5350 -R "$here" -o "$out/$mod.olean" "$here/$mod.lean" 2>&1 | tee "$out/$mod.log"
done
rg -Fxq "'PA194AX11HHaltFrame.fromFlag' depends on axioms: [propext, Classical.choice, Quot.sound]" \
  "$out/PA194AX11HHaltFrame.log"
printf '%s\n' "$LEAN_PATH" >"$out/leanpath.txt"
