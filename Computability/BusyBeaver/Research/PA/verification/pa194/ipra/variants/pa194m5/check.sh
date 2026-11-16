#!/usr/bin/env bash
set -euo pipefail
ulimit -s unlimited
ulimit -c 0

repo=$(cd -- "${1:?repository root required}" && pwd)
model=$(cd -- "${2:?staged PA194 model dependencies required}" && pwd)
out=${3:?fresh output directory required}
here=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
test ! -e "$out"
mkdir -p "$out"
out=$(cd -- "$out" && pwd)

export LEAN_PATH="$(python3 -I - "$out" "$model" <<'PY'
from pathlib import Path
import sys

out, provider = sys.argv[1:]
path = [out, provider, *(Path(provider) / "leanpath.txt").read_text().strip().split(":")]
ordered = list(dict.fromkeys(directory for directory in path if directory))
if not any((Path(directory) / "PA194ModelMPDrain.olean").is_file() for directory in ordered):
    raise SystemExit("The provided model closure must expose PA194ModelMPDrain.olean")
print(":".join(ordered))
PY
)"
printf '%s\n' "$LEAN_PATH" > "$out/leanpath.txt"
python3 -I "$here/generate.py" "$repo" "$out" 5

check() {
  local source=$1 module=$2
  local log="$out/$module.log"
  if ! lean -j1 -M5000 -R "$(dirname -- "$source")" -o "$out/$module.olean" "$source" > "$log" 2>&1; then
    cat "$log"
    return 1
  fi
  cat "$log"
  if rg -q "error:|sorryAx|Lean.ofReduceBool|declaration uses 'sorry'" "$log"; then return 1; fi
  printf 'PASS %s\n' "$module"
}
check "$here/PA194ProgramDrain.lean" PA194ProgramDrain
check "$out/PA194M5Program.lean" PA194M5Program
check "$out/PA194M5Constructor.lean" PA194M5Constructor
rg -Fxq "'PA194ProgramDrain.rowStep' depends on axioms: [propext, Classical.choice, Quot.sound]" "$out/PA194ProgramDrain.log"
rg -Fxq "'PA194ProgramDrain.drain' depends on axioms: [propext, Classical.choice, Quot.sound]" "$out/PA194ProgramDrain.log"
rg -Fxq "'PA194ProgramDrain.multiply' depends on axioms: [propext, Classical.choice, Quot.sound]" "$out/PA194ProgramDrain.log"
rg -Fxq "'PA194M5Constructor.loopRows' depends on axioms: [propext]" "$out/PA194M5Constructor.log"
rg -Fxq "'PA194M5Constructor.firstMultiply' depends on axioms: [propext, Classical.choice, Quot.sound]" "$out/PA194M5Constructor.log"
sha256sum "$here/PA194ProgramDrain.lean" "$here/generate.py" "$here/check.sh" \
  "$out"/PA194M5{Program,Constructor}.lean "$out"/*.olean > "$out/sha256.txt"
