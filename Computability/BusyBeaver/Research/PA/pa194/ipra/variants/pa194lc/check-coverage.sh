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

python3 -I "$here/../generate-linear-coverage.py" PA194LC "$out"
for source in "$out"/PA194LCCoverage[0-9][0-9].lean "$out/PA194LCCoverage.lean"; do
  mod=${source##*/}
  mod=${mod%.lean}
  log="$out/$mod.log"
  if ! lean -j1 -M5350 -R "$out" -o "$out/$mod.olean" "$source" > "$log" 2>&1; then
    head -45 "$log"
    exit 1
  fi
  cat "$log"
  if rg -q "error:|sorryAx|Lean.ofReduceBool|declaration uses 'sorry'" "$log"; then
    exit 1
  fi
  printf 'PASS %s\n' "$mod"
done
rg -Fxq "'PA194LCCoverage.checked' depends on axioms: [propext, Quot.sound]" "$out/PA194LCCoverage.log"
printf '%s\n' "$LEAN_PATH" > "$out/leanpath.txt"
