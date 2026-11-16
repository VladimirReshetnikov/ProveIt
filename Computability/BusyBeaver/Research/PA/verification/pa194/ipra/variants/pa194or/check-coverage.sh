#!/usr/bin/env bash
set -euo pipefail
ulimit -s unlimited
ulimit -c 0

controller=$(cd -- "${1:?verified PA194OR controller stage required}" && pwd)
out=${2:?fresh output directory required}
here=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
repo=$(git -C "$here" rev-parse --show-toplevel)
mkdir -p "$out"
out=$(cd -- "$out" && pwd)
cd "$repo"

export LEAN_PATH="$out:$(cat "$controller/leanpath.txt")"

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

python3 -I "$here/generate-coverage.py" "$out"
# The two workers write to disjoint output files.
blocks=("$out"/PA194ORCoverage[0-9][0-9].lean)
check_blocks() {
  local i
  for ((i=$1; i<${#blocks[@]}; i+=2)); do
    check "${blocks[i]}" || return 1
  done
}
check_blocks 0 &
even=$!
check_blocks 1 &
odd=$!
result=0
wait "$even" || result=1
wait "$odd" || result=1
((result == 0))

check "$out/PA194ORCoverage.lean"
check "$here/PA194ORModelFinal.lean"
rg -Fxq "'PA194ORModelFinal.halt_iff_controller' depends on axioms: [propext, Classical.choice, Quot.sound]" \
  "$out/PA194ORModelFinal.log"
printf '%s\n' "$LEAN_PATH" > "$out/leanpath.txt"
