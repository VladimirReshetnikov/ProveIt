#!/usr/bin/env bash
set -euo pipefail
ulimit -s unlimited
ulimit -c 0

candidate=${1:?candidate (PA194P5, PA194TDY, or PA194C32) required}
case "$candidate" in
  PA194P5 | PA194TDY | PA194C32) ;;
  *) printf 'Unknown candidate %s\n' "$candidate" >&2; exit 2 ;;
esac
model=$(cd -- "${2:?checked selector model stage required}" && pwd)
out=${3:?fresh output directory required}
here=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
repo=$(git -C "$here" rev-parse --show-toplevel)
mkdir -p "$out"
out=$(cd -- "$out" && pwd)
cd "$repo"
export LEAN_PATH="$out:$(cat "$model/leanpath.txt")"

python3 -I "$here/generate-selector-coverage.py" "$candidate" "$out"
for source in "$out"/"${candidate}Coverage"[0-9][0-9].lean "$out/${candidate}CoverageAll.lean"; do
  mod=${source##*/}
  mod=${mod%.lean}
  log="$out/$mod.log"
  if ! lean -j1 -M5250 -R "$out" -o "$out/$mod.olean" "$source" > "$log" 2>&1; then
    head -45 "$log"
    exit 1
  fi
  cat "$log"
  if rg -q "error:|sorryAx|Lean.ofReduceBool|declaration uses 'sorry'" "$log"; then
    exit 1
  fi
  printf 'PASS %s\n' "$mod"
done
rg -Fxq "'${candidate}CoverageAll.checked' depends on axioms: [propext, Classical.choice, Quot.sound]" \
  "$out/${candidate}CoverageAll.log"
printf '%s\n' "$LEAN_PATH" > "$out/leanpath.txt"
