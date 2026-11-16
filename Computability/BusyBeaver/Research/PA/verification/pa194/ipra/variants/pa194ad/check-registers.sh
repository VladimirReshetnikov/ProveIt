#!/usr/bin/env bash
set -euo pipefail
ulimit -s unlimited
ulimit -c 0

register=$(cd -- "${1:?verified shared register stage required}" && pwd)
startup=$(cd -- "${2:?verified PA194-AD startup stage required}" && pwd)
out=${3:?fresh output directory required}
here=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
repo=$(git -C "$here" rev-parse --show-toplevel)
mkdir -p "$out"
out=$(cd -- "$out" && pwd)
cd "$repo"
export LEAN_PATH="$out:$startup:$(cat "$register/leanpath.txt")"

check() {
  local source=$1
  local mod=${source##*/}
  mod=${mod%.lean}
  local log="$out/$mod.log"
  if ! lean -j1 -M5600 -R "$(dirname -- "$source")" -o "$out/$mod.olean" "$source" > "$log" 2>&1; then
    cat "$log"
    return 1
  fi
  cat "$log"
  if rg -q "error:|sorryAx|Lean.ofReduceBool|declaration uses 'sorry'" "$log"; then
    return 1
  fi
  printf 'PASS %s\n' "$mod"
}

python3 -I "$here/bind_tables.py" "$repo" "$out" --compressed
check "$out/PA194ADCompressedData.lean"
for mod in PA194ADCompressedRows PA194ADCompressedChecks PA194ADCompressedPhysical PA194ADDecrementRows PA194ADIncrementRows PA194ADBoxAgreement; do
  check "$here/$mod.lean"
done
rg -Fxq "'PA194ADBoxAgreement.concreteBoxAgreement' depends on axioms: [propext, Classical.choice, Quot.sound]" \
  "$out/PA194ADBoxAgreement.log"
printf '%s\n' "$LEAN_PATH" > "$out/leanpath.txt"
