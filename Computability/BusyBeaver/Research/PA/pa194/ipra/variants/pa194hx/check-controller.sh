#!/usr/bin/env bash
set -euo pipefail
ulimit -s unlimited
ulimit -c 0

register=$(cd -- "${1:?verified PA194HX register stage required}" && pwd)
out=${2:?fresh output directory required}
here=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
repo=$(git -C "$here" rev-parse --show-toplevel)
mkdir -p "$out"
out=$(cd -- "$out" && pwd)
cd "$repo"
export LEAN_PATH="$out:$(cat "$register/leanpath.txt")"

check() {
  local source=$1
  local mod=${source##*/}
  mod=${mod%.lean}
  local log="$out/$mod.log"
  if ! lean -j1 -M5600 -R "$(dirname -- "$source")" -o "$out/$mod.olean" "$source" > "$log" 2>&1; then
    head -45 "$log"
    return 1
  fi
  cat "$log"
  if rg -q "error:|sorryAx|Lean.ofReduceBool|declaration uses 'sorry'" "$log"; then
    return 1
  fi
  printf 'PASS %s\n' "$mod"
}

for mod in ControllerStepAt ControllerAdvance ControllerHalt SourceEndpoint; do
  check "$here/PA194HX$mod.lean"
done
check "$here/../PA194ControllerNative.lean"
check "$here/PA194HXNative.lean"
rg -Fxq "'PA194HXNative.consistency_iff_literal_nonhalt' depends on axioms: [propext, Classical.choice, Quot.sound]" \
  "$out/PA194HXNative.log"
printf '%s\n' "$LEAN_PATH" > "$out/leanpath.txt"
