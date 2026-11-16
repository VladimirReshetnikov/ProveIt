#!/usr/bin/env bash
set -euo pipefail
ulimit -s unlimited
ulimit -c 0

foundation=$(cd -- "${1:?checked PA194HX controller stage required}" && pwd)
contracts=$(cd -- "${2:?checked PA194LC table stage required}" && pwd)
out=${3:?fresh output directory required}
here=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
repo=$(git -C "$here" rev-parse --show-toplevel)
mkdir -p "$out"
out=$(cd -- "$out" && pwd)
cd "$repo"
export LEAN_PATH="$out:$contracts:$(cat "$foundation/leanpath.txt")"

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

python3 -I "$here/../generate-selector-table.py" PA194P5 "$repo" "$out"
check "$out/PA194P5Data.lean"
check "$here/../PA194IndexedNumerals.lean"
for mod in Rows DecrementRows IncrementRows BoxAgreement; do
  check "$here/PA194P5$mod.lean"
done
check "$here/../PA194RegisterLayout.lean"
check "$here/PA194P5Allocation.lean"
for mod in Root Contracts RootEncoding ControllerStep ControllerAdvance; do
  check "$here/../PA194Register$mod.lean"
done
check "$here/../PA194RegisterControllerEndpoint.lean"
check "$here/PA194P5Representative.lean"

python3 -I "$here/../generate-indexed-startup.py" PA194P5 "$repo" "$out"
check "$here/PA194P5Numerical.lean"
for source in "$out"/PA194P5StartupChunk*.lean "$out/PA194P5StartupComplete.lean"; do
  check "$source"
done
for mod in ModelStartup Seed SourceEndpoint; do
  check "$here/PA194P5$mod.lean"
done
rg -Fxq "'PA194P5SourceEndpoint.endpoint' depends on axioms: [propext, Classical.choice, Quot.sound]" \
  "$out/PA194P5SourceEndpoint.log"
printf '%s\n' "$LEAN_PATH" > "$out/leanpath.txt"
