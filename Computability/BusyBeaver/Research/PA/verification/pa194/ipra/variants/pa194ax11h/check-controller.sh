#!/usr/bin/env bash
set -euo pipefail
ulimit -s unlimited
ulimit -c 0

physical=$(cd -- "${1:?checked AX11H physical stage required}" && pwd)
out=${2:?fresh output directory required}
here=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
mkdir -p "$out"
out=$(cd -- "$out" && pwd)
export LEAN_PATH="$out:$(cat "$physical/leanpath.txt")"

for source in "$here/../PA194VariantController.lean" "$here/../PA194TrieSourceController.lean" \
    "$here/PA194AX11HController.lean"; do
  mod=${source##*/}
  mod=${mod%.lean}
  log="$out/$mod.log"
  if ! lean -j1 -M5350 -R "$(dirname -- "$source")" -o "$out/$mod.olean" "$source" >"$log" 2>&1; then
    cat "$log"
    exit 1
  fi
  cat "$log"
  if rg -q "error:|sorryAx|Lean.ofReduceBool|declaration uses 'sorry'" "$log"; then exit 1; fi
  printf 'PASS %s\n' "$mod"
done
rg -Fxq "'PA194AX11HController.halt_iff_site10' depends on axioms: [propext, Classical.choice, Quot.sound]" \
  "$out/PA194AX11HController.log"
printf '%s\n' "$LEAN_PATH" >"$out/leanpath.txt"
