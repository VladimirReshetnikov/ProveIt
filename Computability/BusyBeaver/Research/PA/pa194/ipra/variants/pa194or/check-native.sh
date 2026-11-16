#!/usr/bin/env bash
set -euo pipefail
ulimit -s unlimited
ulimit -c 0

coverage=$(cd -- "${1:?verified PA194OR coverage stage required}" && pwd)
out=${2:?fresh output directory required}
here=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
repo=$(git -C "$here" rev-parse --show-toplevel)
mkdir -p "$out"
out=$(cd -- "$out" && pwd)
cd "$repo"

export LEAN_PATH="$out:$(cat "$coverage/leanpath.txt")"

check() {
  local source=$1
  local mod=${source##*/}
  mod=${mod%.lean}
  local log="$out/$mod.log"
  lean -j1 -M5250 -R "$(dirname -- "$source")" -o "$out/$mod.olean" "$source" > "$log" 2>&1 \
    || { cat "$log"; return 1; }
  cat "$log"
  if rg -q "error:|sorryAx|Lean.ofReduceBool|declaration uses 'sorry'" "$log"; then
    return 1
  fi
  printf 'PASS %s\n' "$mod"
}

check "$here/PA194ORNonhalt.lean"
check "$here/PA194ORFinal.lean"
rg -Fxq "'PA194ORFinal.consistency_iff_literal_nonhalt' depends on axioms: [propext, Classical.choice, Quot.sound]" \
  "$out/PA194ORFinal.log"
