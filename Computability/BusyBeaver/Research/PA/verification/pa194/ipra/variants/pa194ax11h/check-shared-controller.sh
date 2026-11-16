#!/usr/bin/env bash
set -euo pipefail
ulimit -s unlimited
ulimit -c 0

ax11h=$(cd -- "${1:?checked AX11H controller stage required}" && pwd)
out=${2:?fresh output directory required}
here=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
test ! -e "$out"
mkdir -p "$out"
out=$(cd -- "$out" && pwd)
export LEAN_PATH="$out:$ax11h:$(cat "$ax11h/leanpath.txt")"

for source in "$here/../PA194SourceContracts.lean" "$here/../PA194TrieRoot.lean" \
    "$here/../PA194VariantController.lean" "$here/../PA194TrieSourceController.lean" \
    "$here/PA194AX11HSharedController.lean"; do
  module=${source##*/}
  module=${module%.lean}
  log="$out/$module.log"
  if ! lean -j1 -M5350 -R "$(dirname -- "$source")" -o "$out/$module.olean" "$source" >"$log" 2>&1; then
    cat "$log"
    exit 1
  fi
  cat "$log"
  if rg -q "error[:(]|sorryAx|Lean.ofReduceBool|declaration uses 'sorry'" "$log"; then exit 1; fi
done
for theorem in startup_root_of_same_seed halt_iff_site10; do
  rg -Fxq "'PA194AX11HSharedController.$theorem' depends on axioms: [propext, Classical.choice, Quot.sound]" \
    "$out/PA194AX11HSharedController.log"
done
printf '%s\n' "$LEAN_PATH" >"$out/leanpath.txt"
