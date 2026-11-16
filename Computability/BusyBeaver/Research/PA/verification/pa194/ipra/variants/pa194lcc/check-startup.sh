#!/usr/bin/env bash
set -euo pipefail
ulimit -s unlimited
ulimit -c 0
base=$(cd -- "${1:?checked LC_C data stage required}" && pwd)
out=${2:?fresh output directory required}
[[ ! -e "$out" ]] || { echo 'Output must be fresh' >&2; exit 2; }
here=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
repo=$(git -C "$here" rev-parse --show-toplevel)
test -f "$base/PA194LCCData.olean"
test -f "$base/leanpath.txt"
mkdir -p "$out"; out=$(cd -- "$out" && pwd)
cd "$repo"
export LEAN_PATH="$out:$base:$(cat "$base/leanpath.txt")"
check() {
  local source=$1 mod=${1##*/} log
  mod=${mod%.lean}; log="$out/$mod.log"
  if ! lean -j1 -M5250 -R "$(dirname -- "$source")" -o "$out/$mod.olean" "$source" > "$log" 2>&1; then cat "$log"; return 1; fi
  cat "$log"
  if rg -q "error:|sorryAx|Lean.ofReduceBool|declaration uses 'sorry'" "$log"; then return 1; fi
  printf 'PASS %s\n' "$mod"
}
python3 -I "$here/../generate-indexed-startup.py" PA194LCC "$repo" "$out"
check "$here/../../../../shared/isigma1-machine/ConPAMachineNumerals.lean"
check "$here/../PA194IndexedNumerals.lean"
check "$here/PA194LCCNumerical.lean"
for source in "$out"/PA194LCCStartupChunk*.lean "$out/PA194LCCStartupComplete.lean"; do check "$source"; done
check "$here/PA194LCCModelStartup.lean"
rg -Fxq "'PA194LCCModelStartup.modeledStartup' depends on axioms: [propext, Classical.choice, Quot.sound]" "$out/PA194LCCModelStartup.log"
printf '%s\n' "$LEAN_PATH" > "$out/leanpath.txt"
