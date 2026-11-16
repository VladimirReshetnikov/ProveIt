#!/usr/bin/env bash
set -euo pipefail
ulimit -s unlimited
ulimit -c 0
base=$(cd -- "${1:?checked LC data stage required}" && pwd)
out=${2:?fresh output directory required}
[[ ! -e "$out" ]] || { echo 'Output must be fresh' >&2; exit 2; }
here=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
repo=$(git -C "$here" rev-parse --show-toplevel)
test -f "$base/PA194LCData.lean"
test -f "$base/PA194LCData.olean"
test -f "$base/leanpath.txt"
mkdir -p "$out"; out=$(cd -- "$out" && pwd)
cd "$repo"
export LEAN_PATH="$out:$base:$(cat "$base/leanpath.txt")"
python3 -I "$here/generate-data.py" "$repo" "$out" "$base/PA194LCData.lean"
cmp "$here/PA194LCCData.lean" "$out/PA194LCCData.lean"
check() {
  local source=$1 mod=${1##*/} log
  mod=${mod%.lean}; log="$out/$mod.log"
  if ! lean -j1 -M6000 -R "$(dirname -- "$source")" -o "$out/$mod.olean" "$source" > "$log" 2>&1; then cat "$log"; return 1; fi
  cat "$log"
  if rg -q "error:|sorryAx|Lean.ofReduceBool|declaration uses 'sorry'" "$log"; then return 1; fi
  printf 'PASS %s\n' "$mod"
}
check "$out/PA194LCCData.lean"
for mod in Rows Checks Physical BoxAgreement Samples; do check "$here/PA194LCC$mod.lean"; done
printf '%s\n' "$LEAN_PATH" > "$out/leanpath.txt"
