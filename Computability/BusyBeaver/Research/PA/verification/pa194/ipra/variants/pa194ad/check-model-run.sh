#!/usr/bin/env bash
set -euo pipefail
ulimit -s unlimited
ulimit -c 0

literal=$(cd -- "${1:?checked primary literal output directory required}" && pwd)
shared=$(cd -- "${2:?checked PA194B output directory required}" && pwd)
ad=$(cd -- "${3:?checked PA194-AD startup output directory required}" && pwd)
out=${4:?output directory required}
here=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
repo=$(git -C "$here" rev-parse --show-toplevel)
mkdir -p "$out"
out=$(cd -- "$out" && pwd)
cd "$repo"

export LEAN_PATH="$out:$ad:$shared:$(cat "$literal/leanpath.txt")"

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

for module in PAVariantRowDispatch PAVariantModelStep PAVariantFixedRow PA194VariantPackedStep; do
  check "$here/../$module.lean"
done
check "$here/PAVariantADInstance.lean"
check "$here/PA194ADGenericRun.lean"
rg -Fxq "'PA194ADGenericRun.clock_run' depends on axioms: [propext, Classical.choice, Quot.sound]" \
  "$out/PA194ADGenericRun.log"
