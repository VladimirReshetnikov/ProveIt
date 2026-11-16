#!/usr/bin/env bash
set -euo pipefail
ulimit -s unlimited
ulimit -c 0

repo=$(cd -- "${1:?repository root required}" && pwd)
final=$(cd -- "${2:?checked PA1944L final stage required}" && pwd)
coverage=$(cd -- "${3:?checked PA1944L coverage stage required}" && pwd)
timing=$(cd -- "${4:?checked guarded timing stage required}" && pwd)
selector=$(cd -- "${5:?checked guarded selector stage required}" && pwd)
relative=$(cd -- "${6:?checked relative native transfer stage required}" && pwd)
out=${7:?fresh output directory required}
here=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)

test -f "$final/PA1944LFinal.olean"
test -f "$coverage/PA1944LCoverage.olean"
test -f "$timing/PA194GuardedShortcuts.olean"
test -f "$selector/PA194GuardedSelectors.olean"
test -f "$relative/ConPAMachineRelative.olean"
test -f "$coverage/leanpath.txt"
test ! -e "$out"
mkdir -p "$out"
out=$(cd -- "$out" && pwd)
cd -- "$repo"

export LEAN_PATH="$(python3 -I - "$out" "$relative" "$final" "$coverage" "$timing" "$selector" <<'PY'
from pathlib import Path
import sys

out, *stages = sys.argv[1:]
paths = [out, *stages]
for stage in stages:
    receipt = Path(stage) / "leanpath.txt"
    if receipt.is_file():
        paths.extend(receipt.read_text().strip().split(":"))
print(":".join(dict.fromkeys(path for path in paths if path)))
PY
)"
printf '%s\n' "$LEAN_PATH" > "$out/leanpath.txt"
python3 -I "$here/generate-rows.py" "$repo" "$out"
python3 -I "$here/generate-history-rows.py" "$repo" "$out"

check() {
  local module=$1 source=$2
  local log="$out/$module.log"
  if ! lean -j1 -M5500 -R "$(dirname -- "$source")" -o "$out/$module.olean" "$source" > "$log" 2>&1; then
    cat "$log"
    exit 1
  fi
  cat "$log"
  if rg -q "error:|sorryAx|Lean.ofReduceBool|declaration uses 'sorry'" "$log"; then exit 1; fi
  printf 'PASS %s\n' "$module"
}

check PA194GuardedHistory "$here/PA194GuardedHistory.lean"
rg -Fxq "'PA194GuardedHistory.sameHalt' depends on axioms: [propext, Classical.choice, Quot.sound]" "$out/PA194GuardedHistory.log"

cases=(Fast SEL FastSEL History FastHistory SELHistory FastSELHistory)
for variant in "${cases[@]}"; do
  module=PA1944L${variant}Rows
  check "$module" "$out/$module.lean"
  rg -Fxq "'$module.certificate' depends on axioms: [propext]" "$out/$module.log"
done

check PA1944LCompanionFinals "$here/PA1944LCompanionFinals.lean"
for variant in "${cases[@]}"; do
  theorem=PA1944L${variant}Final.consistency_iff_literal_nonhalt
  rg -Fxq "'$theorem' depends on axioms: [propext, Classical.choice, Quot.sound]" \
    "$out/PA1944LCompanionFinals.log"
done

sha256sum "$here"/*.lean "$here"/generate*.py "$here/check.sh" \
  "$out"/*.lean "$out"/*.native.tm "$out"/*.olean \
  "$final/PA1944LFinal.olean" "$coverage/PA1944LCoverage.olean" \
  "$timing/PA194GuardedShortcuts.olean" "$selector/PA194GuardedSelectors.olean" \
  "$relative/ConPAMachineRelative.olean" > "$out/sha256.txt"
