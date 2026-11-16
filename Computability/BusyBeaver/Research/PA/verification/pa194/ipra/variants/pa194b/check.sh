#!/usr/bin/env bash
set -euo pipefail
ulimit -s unlimited
ulimit -c 0

literal=$(cd -- "${1:?checked primary literal output directory required}" && pwd)
out=${2:?output directory required}
here=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
repo=$(git -C "$here" rev-parse --show-toplevel)
pa="$repo/Computability/BusyBeaver/Research/PA/verification"
shared="$pa/shared/isigma1-machine"
machine="$pa/pa194/ipra/machine-code"
mkdir -p "$out"
out=$(cd -- "$out" && pwd)
cd "$repo"

test -f "$literal/PA194NativeLiteralFinal.olean"
export LEAN_PATH="$out:$literal:$(cat "$literal/leanpath.txt")"

python3 -I "$here/generate-rows.py" "$repo" "$out/PA194BRows.lean"
cmp "$here/PA194BRows.lean" "$out/PA194BRows.lean"

check() {
  local source=$1
  local mod=${source##*/}
  mod=${mod%.lean}
  local log="$out/$mod.log"
  if ! lean -j1 -M6000 -R "$(dirname -- "$source")" -o "$out/$mod.olean" "$source" > "$log" 2>&1; then
    cat "$log"
    return 1
  fi
  cat "$log"
  if rg -q "error:|sorryAx|Lean.ofReduceBool|declaration uses 'sorry'" "$log"; then
    return 1
  fi
  printf 'PASS %s\n' "$mod"
}

check "$shared/ConPAISigma1Relative.lean"
check "$shared/ConPAMachineStutter.lean"
check "$machine/PA194GenericHalt.lean"
check "$here/../PA194VariantNative.lean"
for module in Rows Finite ModelSteps Exceptions Relation Segment Halting Native; do
  check "$here/PA194B$module.lean"
done
rg -Fxq "'PA194BNative.consistency_iff_literal_nonhalt' depends on axioms: [propext, Classical.choice, Quot.sound]" \
  "$out/PA194BNative.log"
printf '%s\n' "$LEAN_PATH" > "$out/leanpath.txt"
