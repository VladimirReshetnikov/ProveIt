#!/usr/bin/env bash
set -euo pipefail
ulimit -s unlimited
ulimit -c 0
input=$(cd -- "${1:?verified trie controller stage required}" && pwd)
out=${2:?fresh output directory required}
here=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
repo=$(git -C "$here" rev-parse --show-toplevel)
mkdir -p "$out"
out=$(cd -- "$out" && pwd)
export LEAN_PATH="$out:$(cat "$input/leanpath.txt")"
check() {
  local source=$1
  local mod=${source##*/}
  mod=${mod%.lean}
  local log="$out/$mod.log"
  if ! lean -j1 -M5350 -R "$(dirname -- "$source")" -o "$out/$mod.olean" "$source" >"$log" 2>&1; then
    head -45 "$log"
    return 1
  fi
  cat "$log"
  if rg -q 'error:|sorryAx|Lean.ofReduceBool|declaration uses .sorry.' "$log"; then
    return 1
  fi
  printf 'PASS %s\n' "$mod"
}
python3 -I "$here/../generate-source-table.py" PA194LCB "$repo" "$out"
python3 -I "$here/../generate-indexed-startup.py" PA194LCB "$repo" "$out"
check "$out/PA194LCBData.lean"
for mod in Rows Checks Physical BoxAgreement Numerical; do
  check "$here/PA194LCB$mod.lean"
done
for source in "$out"/PA194LCBStartupChunk*.lean "$out/PA194LCBStartupComplete.lean"; do
  check "$source"
done
for mod in ModelStartup Controller Initializer; do
  check "$here/PA194LCB$mod.lean"
done
printf '%s\n' "$LEAN_PATH" >"$out/leanpath.txt"
