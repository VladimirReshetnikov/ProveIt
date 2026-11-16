#!/usr/bin/env bash
set -euo pipefail
ulimit -s unlimited
ulimit -c 0

literal=$(cd -- "${1:?verified primary literal stage required}" && pwd)
shared=$(cd -- "${2:?verified PA194B stage required}" && pwd)
execution=$(cd -- "${3:?verified compressed execution stage required}" && pwd)
out=${4:?fresh output directory required}
here=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
repo=$(git -C "$here" rev-parse --show-toplevel)
mkdir -p "$out"
out=$(cd -- "$out" && pwd)
cd "$repo"

export LEAN_PATH="$out:$execution:$shared:$(cat "$literal/leanpath.txt")"

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

python3 -I "$here/generate-table.py" "$repo" "$out"
python3 -I "$here/generate-startup.py" "$repo" "$out"
check "$here/../../../../shared/isigma1-machine/ConPAMachineNumerals.lean"
check "$here/../PA194IndexedNumerals.lean"
check "$out/PA194ORData.lean"
for module in Numerical Rows Checks Physical Mark MovedFirst MovedSecond; do
  check "$here/PA194OR$module.lean"
done
for chunk in "$out"/PA194ORStartupChunk*.lean; do
  check "$chunk"
done
check "$out/PA194ORStartupComplete.lean"
check "$here/PA194ORModelStartup.lean"
rg -Fxq "'PA194ORModelStartup.modeledStartup' depends on axioms: [propext, Classical.choice, Quot.sound]" \
  "$out/PA194ORModelStartup.log"
