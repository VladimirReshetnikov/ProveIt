#!/usr/bin/env bash
set -euo pipefail
ulimit -s unlimited
ulimit -c 0
startup=$(cd -- "${1:?checked LC_C startup stage required}" && pwd)
out=${2:?fresh output directory required}
[[ ! -e "$out" ]] || { echo 'Output must be fresh' >&2; exit 2; }
here=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
repo=$(git -C "$here" rev-parse --show-toplevel)
test -f "$startup/PA194LCCModelStartup.olean"
test -f "$startup/leanpath.txt"
mkdir -p "$out"; out=$(cd -- "$out" && pwd)
cd "$repo"
export LEAN_PATH="$out:$startup:$(cat "$startup/leanpath.txt")"
check() {
  local source=$1 mod=${1##*/} log
  mod=${mod%.lean}; log="$out/$mod.log"
  if ! lean -j1 -M6000 -R "$(dirname -- "$source")" -o "$out/$mod.olean" "$source" > "$log" 2>&1; then cat "$log"; return 1; fi
  cat "$log"
  if rg -q "error:|sorryAx|Lean.ofReduceBool|declaration uses 'sorry'" "$log"; then return 1; fi
  printf 'PASS %s\n' "$mod"
}
check "$here/../PA194SourceContracts.lean"
check "$here/../PA194TrieRoot.lean"
check "$here/../PA194VariantController.lean"
check "$here/../PA194TrieSourceController.lean"
check "$here/PA194LCCController.lean"
check "$here/PA194LCCInitializer.lean"
check "$here/../PA194ControllerNative.lean"
check "$here/PA194LCCNative.lean"
rg -Fxq "'PA194LCCNative.consistency_iff_literal_nonhalt' depends on axioms: [propext, Classical.choice, Quot.sound]" "$out/PA194LCCNative.log"
printf '%s\n' "$LEAN_PATH" > "$out/leanpath.txt"
