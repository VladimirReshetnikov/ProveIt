#!/usr/bin/env bash
set -euo pipefail
ulimit -s unlimited
ulimit -c 0
controller=$(cd -- "${1:?checked LC_C controller stage required}" && pwd)
out=${2:?fresh output directory required}
[[ ! -e "$out" ]] || { echo 'Output must be fresh' >&2; exit 2; }
here=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
repo=$(git -C "$here" rev-parse --show-toplevel)
test -f "$controller/PA194LCCNative.olean"
test -f "$controller/leanpath.txt"
mkdir -p "$out"; out=$(cd -- "$out" && pwd)
cd "$repo"
export LEAN_PATH="$out:$controller:$(cat "$controller/leanpath.txt")"
python3 -I "$here/../generate-linear-coverage.py" PA194LCC "$out"
for source in "$out"/PA194LCCCoverage[0-9][0-9].lean "$out/PA194LCCCoverage.lean" "$here/PA194LCCFinal.lean"; do
  mod=${source##*/}; mod=${mod%.lean}; log="$out/$mod.log"
  if ! lean -j1 -M5350 -R "$(dirname -- "$source")" -o "$out/$mod.olean" "$source" > "$log" 2>&1; then cat "$log"; exit 1; fi
  cat "$log"
  if rg -q "error:|sorryAx|Lean.ofReduceBool|declaration uses 'sorry'" "$log"; then exit 1; fi
  printf 'PASS %s\n' "$mod"
done
rg -Fxq "'PA194LCCFinal.consistency_iff_literal_nonhalt' depends on axioms: [propext, Classical.choice, Quot.sound]" "$out/PA194LCCFinal.log"
printf '%s\n' "$LEAN_PATH" > "$out/leanpath.txt"
