#!/usr/bin/env bash
set -euo pipefail
ulimit -s unlimited
ulimit -c 0

candidate=${1:?candidate required}
rows=$(cd -- "${2:?checked selector row stage required}" && pwd)
parent=$(cd -- "${3:?checked parent theorem stage required}" && pwd)
bridge=$(cd -- "${4:?checked machine relative transfer stage required}" && pwd)
out=${5:?output directory required}
here=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
mkdir -p "$out"
out=$(cd -- "$out" && pwd)
python3 -I "$here/generate-native.py" "$candidate" "$out"
export LEAN_PATH="$(python3 -I - "$out" "$bridge" "$rows" "$parent" <<'PY'
from pathlib import Path
import sys

out, *stages = sys.argv[1:]
paths = [out, *stages]
for stage in stages:
    recorded = Path(stage) / "leanpath.txt"
    if recorded.is_file():
        paths.extend(recorded.read_text().strip().split(":"))
print(":".join(dict.fromkeys(path for path in paths if path)))
PY
)"

module=PA194${candidate}SELFinal
log="$out/$module.log"
if ! lean -j1 -M5500 -R "$out" -o "$out/$module.olean" "$out/$module.lean" >"$log" 2>&1; then
  cat "$log"
  exit 1
fi
cat "$log"
if rg -q "error:|sorryAx|Lean.ofReduceBool|declaration uses 'sorry'" "$log"; then exit 1; fi
rg -Fxq "'$module.consistency_iff_literal_nonhalt' depends on axioms: [propext, Classical.choice, Quot.sound]" "$log"
printf '%s\n' "$LEAN_PATH" >"$out/leanpath.txt"
printf 'PASS %s\n' "$module"
