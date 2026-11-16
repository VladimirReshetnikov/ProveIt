#!/usr/bin/env bash
set -euo pipefail
ulimit -s unlimited
ulimit -c 0

register=$(cd -- "${1:?verified shared PA194 register stage required}" && pwd)
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
  if ! lean -j1 -M5250 -R "$(dirname -- "$source")" -o "$out/$mod.olean" "$source" > "$log" 2>&1; then
    head -45 "$log"
    return 1
  fi
  cat "$log"
  if rg -q "error:|sorryAx|Lean.ofReduceBool|declaration uses 'sorry'" "$log"; then
    return 1
  fi
  printf 'PASS %s\n' "$mod"
}

python3 -I "$here/../generate-source-table.py" PA194LC "$repo" "$out"
check "$out/PA194LCData.lean"
check "$here/../PA194TableRows.lean"
check "$here/../PA194SourceContracts.lean"
check "$here/../PA194TrieRoot.lean"
for mod in Rows Checks Physical BoxAgreement Samples; do
  check "$here/PA194LC$mod.lean"
done
printf '%s\n' "$LEAN_PATH" > "$out/leanpath.txt"
