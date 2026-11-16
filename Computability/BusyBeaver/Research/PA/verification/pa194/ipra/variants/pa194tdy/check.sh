#!/usr/bin/env bash
set -euo pipefail
ulimit -s unlimited
ulimit -c 0

foundation=$(cd -- "${1:?checked PA194P5 model stage required}" && pwd)
out=${2:?fresh output directory required}
here=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
repo=$(git -C "$here" rev-parse --show-toplevel)
mkdir -p "$out"
out=$(cd -- "$out" && pwd)
cd "$repo"
export LEAN_PATH="$out:$(cat "$foundation/leanpath.txt")"

check() {
  local source=$1
  local mod=${source##*/}
  mod=${mod%.lean}
  local log="$out/$mod.log"
  if ! lean -j1 -M5250 -R "$(dirname -- "$source")" -o "$out/$mod.olean" "$source" > "$log" 2>&1; then
    head -45 "$log"
    return 1
  fi
  cat "$log"
  if rg -q "error:|sorryAx|Lean.ofReduceBool|declaration uses 'sorry'" "$log"; then
    return 1
  fi
  printf 'PASS %s\n' "$mod"
}

python3 -I "$here/../generate-selector-table.py" PA194TDY "$repo" "$out"
check "$out/PA194TDYData.lean"
for mod in Rows DecrementRows IncrementRows BoxAgreement Allocation Checks; do
  check "$here/PA194TDY$mod.lean"
done
check "$here/../PA194RegisterControllerEndpoint.lean"

python3 -I "$here/../generate-indexed-startup.py" PA194TDY "$repo" "$out"
check "$here/PA194TDYNumerical.lean"
for source in "$out"/PA194TDYStartupChunk*.lean "$out/PA194TDYStartupComplete.lean"; do
  check "$source"
done
for mod in ModelStartup Seed SourceEndpoint; do
  check "$here/PA194TDY$mod.lean"
done
rg -Fxq "'PA194TDYSourceEndpoint.endpoint' depends on axioms: [propext, Classical.choice, Quot.sound]" +  "$out/PA194TDYSourceEndpoint.log"
printf '%s\n' "$LEAN_PATH" > "$out/leanpath.txt"
