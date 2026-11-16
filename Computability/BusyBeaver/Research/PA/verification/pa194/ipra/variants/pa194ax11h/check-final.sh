#!/usr/bin/env bash
set -euo pipefail
ulimit -s unlimited
ulimit -c 0

native=$(cd -- "${1:?checked native transfer required}" && pwd)
shift=$(cd -- "${2:?checked SHIFT and returning-command stage required}" && pwd)
axiom=$(cd -- "${3:?checked axiom frame required}" && pwd)
rows=$(cd -- "${4:?checked axiom body row certificate required}" && pwd)
out=${5:?fresh output directory required}
here=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
mkdir -p "$out"
out=$(cd -- "$out" && pwd)
export LEAN_PATH="$(python3 - "$out" "$native" "$shift" "$axiom" "$rows" <<'PY'
from pathlib import Path
import sys

out, *stages = map(Path, sys.argv[1:])
paths = [str(p) for p in (out, *stages)]
for stage in stages:
    paths.extend((stage / 'leanpath.txt').read_text().strip().split(':'))
print(':'.join(dict.fromkeys(p for p in paths if p)))
PY
)"
mod=PA194AX11HFinal
log="$out/$mod.log"
lean -j1 -M5500 -R "$here" -o "$out/$mod.olean" "$here/$mod.lean" 2>&1 | tee "$log"
rg -Fxq "'$mod.consistency_iff_literal_nonhalt' depends on axioms: [propext, Classical.choice, Quot.sound]" "$log"
printf '%s\n' "$LEAN_PATH" >"$out/leanpath.txt"
