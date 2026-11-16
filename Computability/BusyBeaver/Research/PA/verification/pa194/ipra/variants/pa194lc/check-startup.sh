#!/usr/bin/env bash
set -euo pipefail
ulimit -s unlimited
ulimit -c 0

base=$(cd -- "${1:?verified PA194LC table stage required}" && pwd)
out=${2:?fresh output directory required}
here=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
repo=$(git -C "$here" rev-parse --show-toplevel)
mkdir -p "$out"
out=$(cd -- "$out" && pwd)
cd "$repo"
export LEAN_PATH="$out:$(cat "$base/leanpath.txt")"

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

python3 -I "$here/../generate-indexed-startup.py" PA194LC "$repo" "$out"
check "$here/../../../../shared/isigma1-machine/ConPAMachineNumerals.lean"
check "$here/../PA194IndexedNumerals.lean"
check "$here/PA194LCNumerical.lean"
for source in "$out"/PA194LCStartupChunk*.lean "$out/PA194LCStartupComplete.lean"; do
  check "$source"
done
check "$here/PA194LCModelStartup.lean"
rg -Fxq "'PA194LCModelStartup.modeledStartup' depends on axioms: [propext, Classical.choice, Quot.sound]" \
  "$out/PA194LCModelStartup.log"
printf '%s\n' "$LEAN_PATH" > "$out/leanpath.txt"
