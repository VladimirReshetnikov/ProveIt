#!/usr/bin/env bash
set -euo pipefail
ulimit -s unlimited
ulimit -c 0
model=$(cd -- "${1:?checked PA194 projections provider required}" && pwd)
out=${2:?fresh output directory required}
here=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
test ! -e "$out"
mkdir -p "$out"
out=$(cd -- "$out" && pwd)
export LEAN_PATH="$out:$model:$(cat "$model/leanpath.txt")"
printf '%s\n' "$LEAN_PATH" > "$out/leanpath.txt"
module=PA194RadixModel
log="$out/$module.log"
if ! lean -j1 -M4500 -R "$here" -o "$out/$module.olean" "$here/$module.lean" > "$log" 2>&1; then
  cat "$log"
  exit 1
fi
cat "$log"
if rg -q "error:|sorryAx|Lean.ofReduceBool|declaration uses 'sorry'" "$log"; then exit 1; fi
for theorem in decoded componentDescent constructorInj reconstruct decoderDescent; do
  rg -Fxq "'$module.$theorem' depends on axioms: [propext, Classical.choice, Quot.sound]" "$log"
done
sha256sum "$here/$module.lean" "$here/check-radix.sh" "$out/$module.olean" > "$out/sha256.txt"
