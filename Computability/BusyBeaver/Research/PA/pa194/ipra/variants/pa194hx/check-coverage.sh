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
  if ! lean -j1 -M5350 -R "$(dirname -- "$source")" -o "$out/$mod.olean" "$source" > "$log" 2>&1; then
    head -45 "$log"
    return 1
  fi
  cat "$log"
  if rg -q "error:|sorryAx|Lean.ofReduceBool|declaration uses 'sorry'" "$log"; then
    return 1
  fi
  printf 'PASS %s\n' "$mod"
}

python3 -I "$here/generate-coverage.py" "$out"
check "$here/PA194HXCoverageFirst.lean"
check "$here/PA194HXCoverageFirstSound.lean"
for source in "$out"/PA194HXCoverage[0-9][0-9].lean "$out/PA194HXCoverageAll.lean"; do
  check "$source"
done
rg -Fxq "'PA194HXCoverageAll.checked' depends on axioms: [propext, Quot.sound]" "$out/PA194HXCoverageAll.log"
printf '%s\n' "$LEAN_PATH" > "$out/leanpath.txt"
