#!/usr/bin/env bash
set -euo pipefail
ulimit -s unlimited
ulimit -c 0

literal=$(cd -- "${1:?checked primary literal output directory required}" && pwd)
shared=$(cd -- "${2:?checked PA194B output directory required}" && pwd)
out=${3:?fresh output directory required}
here=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
repo=${4:-}
if [[ -z "$repo" ]]; then
  repo=$(git -C "$here" rev-parse --show-toplevel)
fi
mkdir -p "$out"
out=$(cd -- "$out" && pwd)

test -f "$literal/PA194NativeLiteralFinal.olean"
test -f "$shared/PA194VariantNative.olean"
export LEAN_PATH="$out:$shared:$literal:$(cat "$literal/leanpath.txt")"
printf '%s\n' "$LEAN_PATH" > "$out/leanpath.txt"
python3 -I "$here/generate.py" "$repo" "$out"

check() {
  local source=$1
  local module=${source##*/}
  module=${module%.lean}
  local log="$out/$module.log"
  if ! lean -j1 -M5500 -R "$(dirname -- "$source")" -o "$out/$module.olean" "$source" > "$log" 2>&1; then
    head -45 "$log"
    return 1
  fi
  cat "$log"
  if rg -q "error:|sorryAx|Lean.ofReduceBool|declaration uses 'sorry'" "$log"; then
    return 1
  fi
  printf 'PASS %s\n' "$module"
}

check "$out/PA194FastRows.lean"
for module in Invariant Segment Native; do
  check "$here/PA194Fast$module.lean"
done
rg -Fxq "'PA194FastNative.consistency_iff_literal_nonhalt' depends on axioms: [propext, Classical.choice, Quot.sound]" \
  "$out/PA194FastNative.log"
