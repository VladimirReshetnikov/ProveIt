#!/usr/bin/env bash
set -euo pipefail
ulimit -s unlimited
ulimit -c 0

literal=$(cd -- "${1:?checked primary literal output directory required}" && pwd)
shared=$(cd -- "${2:?checked PA194B output directory required}" && pwd)
out=${3:?output directory required}
here=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
repo=$(git -C "$here" rev-parse --show-toplevel)
mkdir -p "$out"
out=$(cd -- "$out" && pwd)
cd "$repo"

test -f "$literal/PA194NativeLiteralFinal.olean"
test -f "$shared/PA194BNative.olean"
export LEAN_PATH="$out:$shared:$literal:$(cat "$literal/leanpath.txt")"

python3 -I "$here/generate-rows.py" "$repo" "$out/PA194SELRows.lean"
cmp "$here/PA194SELRows.lean" "$out/PA194SELRows.lean"

for module in Rows Finite Relation Segment Halting Native; do
  mod="PA194SEL$module"
  log="$out/$mod.log"
  if ! lean -j1 -M6000 -R "$here" -o "$out/$mod.olean" "$here/$mod.lean" > "$log" 2>&1; then
    cat "$log"
    exit 1
  fi
  cat "$log"
  if rg -q "error:|sorryAx|Lean.ofReduceBool|declaration uses 'sorry'" "$log"; then
    exit 1
  fi
  printf 'PASS %s\n' "$mod"
done
rg -Fxq "'PA194SELNative.consistency_iff_literal_nonhalt' depends on axioms: [propext, Classical.choice, Quot.sound]" \
  "$out/PA194SELNative.log"
