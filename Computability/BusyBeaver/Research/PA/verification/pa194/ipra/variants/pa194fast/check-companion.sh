#!/usr/bin/env bash
set -euo pipefail
ulimit -s unlimited
ulimit -c 0

candidate=${1:?candidate AD, HX, LC, or LCC required}
base=$(cd -- "${2:?checked candidate controller output required}" && pwd)
coverage=$(cd -- "${3:?candidate coverage/source provider required}" && pwd)
out=${4:?fresh output directory required}
repo=$(cd -- "${5:?repository directory required}" && pwd)
here=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
engine="$repo/Computability/BusyBeaver/Research/PA/verification/pa194/ipra/variants/pa194fast/PA194GuardedShortcuts.lean"
mkdir -p "$out"
out=$(cd -- "$out" && pwd)
export LEAN_PATH="$(python3 -I - "$out" "$coverage" "$base" <<'PYTHON'
from pathlib import Path
import sys

out, coverage, base = sys.argv[1:]
paths = [out, coverage, base]
for provider in (coverage, base):
    recorded = Path(provider) / "leanpath.txt"
    if recorded.is_file():
        paths.extend(recorded.read_text().strip().split(":"))
print(":".join(dict.fromkeys(p for p in paths if p)))
PYTHON
)"
printf '%s\n' "$LEAN_PATH" > "$out/leanpath.txt"
python3 -I "$here/generate-rows.py" "$repo" "$out" --only "$candidate"

check() {
  local source=$1 mod
  mod=${source##*/}
  mod=${mod%.lean}
  local log="$out/$mod.log"
  if ! lean -j1 -M5500 -R "$(dirname -- "$source")" -o "$out/$mod.olean" "$source" > "$log" 2>&1; then
    head -45 "$log"
    return 1
  fi
  cat "$log"
  if rg -q "error:|sorryAx|Lean.ofReduceBool|declaration uses 'sorry'" "$log"; then return 1; fi
  printf 'PASS %s\n' "$mod"
}

check "$engine"
check "$out/PA194${candidate}FastRows.lean"
check "$here/PA194FastController.lean"
check "$here/PA194${candidate}FastNative.lean"
rg -Fxq "'PA194${candidate}FastNative.consistency_iff_literal_nonhalt' depends on axioms: [propext, Classical.choice, Quot.sound]" \
  "$out/PA194${candidate}FastNative.log"
if [[ "$candidate" == LCC ]]; then
  check "$here/PA194LCCFastFinal.lean"
  rg -Fxq "'PA194LCCFastFinal.consistency_iff_literal_nonhalt' depends on axioms: [propext, Classical.choice, Quot.sound]" \
    "$out/PA194LCCFastFinal.log"
fi
