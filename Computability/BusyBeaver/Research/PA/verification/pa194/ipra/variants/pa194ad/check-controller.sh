#!/usr/bin/env bash
set -euo pipefail
ulimit -s unlimited
ulimit -c 0

register=$(cd -- "${1:?verified PA194-AD register stage required}" && pwd)
model=$(cd -- "${2:?verified PA194-AD model run stage required}" && pwd)
out=${3:?fresh output directory required}
here=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
repo=$(git -C "$here" rev-parse --show-toplevel)
mkdir -p "$out"
out=$(cd -- "$out" && pwd)
cd "$repo"
export LEAN_PATH="$out:$model:$(cat "$register/leanpath.txt")"

check() {
  local source=$1
  local mod=${source##*/}
  mod=${mod%.lean}
  local log="$out/$mod.log"
  if ! lean -j1 -M5600 -R "$(dirname -- "$source")" -o "$out/$mod.olean" "$source" > "$log" 2>&1; then
    cat "$log"
    return 1
  fi
  cat "$log"
  if rg -q "error:|sorryAx|Lean.ofReduceBool|declaration uses 'sorry'" "$log"; then
    return 1
  fi
  printf 'PASS %s\n' "$mod"
}

for mod in PA194ADSourceArgs PA194ADRoot PA194ADController PA194ADInitializer PA194ADControllerEndpoint; do
  check "$here/$mod.lean"
done
check "$here/../PA194ControllerNative.lean"
check "$here/PA194ADNative.lean"
rg -Fxq "'PA194ADNative.consistency_iff_literal_nonhalt' depends on axioms: [propext, Classical.choice, Quot.sound]" \
  "$out/PA194ADNative.log"
printf '%s\n' "$LEAN_PATH" > "$out/leanpath.txt"
