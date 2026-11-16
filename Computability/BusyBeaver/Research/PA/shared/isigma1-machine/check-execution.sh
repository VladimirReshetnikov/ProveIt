#!/usr/bin/env bash
set -euo pipefail
ulimit -s unlimited
ulimit -c 0

literal=$(cd -- "${1:?checked primary literal output directory required}" && pwd)
shared=$(cd -- "${2:?checked PA194B output directory required}" && pwd)
out=${3:?output directory required}
here=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
repo=$(git -C "$here" rev-parse --show-toplevel)
mkdir -p "$out"
out=$(cd -- "$out" && pwd)
cd "$repo"

export LEAN_PATH="$out:$shared:$(cat "$literal/leanpath.txt")"

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

for module in Segments Scans SourceSimulation CompressedTape CompressedExecutor CompressedNormalization; do
  check "$here/ConPAMachine$module.lean"
done
check "$here/../../pa194/ipra/variants/PA194VariantController.lean"
rg -Fxq "'PA194VariantController.halt_iff_controller' depends on axioms: [propext, Classical.choice, Quot.sound]" \
  "$out/PA194VariantController.log"
