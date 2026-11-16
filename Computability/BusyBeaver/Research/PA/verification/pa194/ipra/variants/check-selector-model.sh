#!/usr/bin/env bash
set -euo pipefail
ulimit -s unlimited
ulimit -c 0

candidate=${1:?candidate (PA194TDY or PA194C32) required}
case "$candidate" in
  PA194TDY | PA194C32) ;;
  *) printf 'Unknown candidate %s\n' "$candidate" >&2; exit 2 ;;
esac
foundation=$(cd -- "${2:?checked PA194P5 model stage required}" && pwd)
out=${3:?fresh output directory required}
here=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
repo=$(git -C "$here" rev-parse --show-toplevel)
dir="$here/${candidate,,}"
mkdir -p "$out"
out=$(cd -- "$out" && pwd)
cd "$repo"
export LEAN_PATH="$out:$(cat "$foundation/leanpath.txt")"

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

python3 -I "$here/generate-selector-table.py" "$candidate" "$repo" "$out"
check "$out/${candidate}Data.lean"
for mod in Rows DecrementRows IncrementRows BoxAgreement Allocation Checks; do
  check "$dir/$candidate$mod.lean"
done
check "$here/PA194RegisterControllerEndpoint.lean"

python3 -I "$here/generate-indexed-startup.py" "$candidate" "$repo" "$out"
check "$dir/${candidate}Numerical.lean"
for source in "$out"/"${candidate}StartupChunk"*.lean "$out/${candidate}StartupComplete.lean"; do
  check "$source"
done
for mod in ModelStartup Seed SourceEndpoint; do
  check "$dir/$candidate$mod.lean"
done
rg -Fxq "'${candidate}SourceEndpoint.endpoint' depends on axioms: [propext, Classical.choice, Quot.sound]" \
  "$out/${candidate}SourceEndpoint.log"
printf '%s\n' "$LEAN_PATH" > "$out/leanpath.txt"
