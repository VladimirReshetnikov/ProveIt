#!/usr/bin/env bash
set -euo pipefail
ulimit -s unlimited
ulimit -c 0

base=$(cd -- "${1:?checked PA1944L model stage required}" && pwd)
out=${2:?output directory required}
here=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
repo=$(git -C "$here" rev-parse --show-toplevel)
test -s "$base/PA1944LData.olean"
mkdir -p "$out"
out=$(cd -- "$out" && pwd)
cd "$repo"
export LEAN_PATH="$out:$(cat "$base/leanpath.txt")"

check() {
  local source=$1 mod=${1##*/} log
  mod=${mod%.lean}
  log="$out/$mod.log"
  if ! lean -j1 -M5350 -R "$(dirname -- "$source")" -o "$out/$mod.olean" "$source" >"$log" 2>&1; then
    cat "$log"
    return 1
  fi
  cat "$log"
  if rg -q "error:|sorryAx|Lean.ofReduceBool|declaration uses 'sorry'" "$log"; then return 1; fi
  printf 'PASS %s\n' "$mod"
}

check "$here/PA194IndexedRunRestriction.lean"
for candidate in PA194LCA PA194M4R; do
  python3 -I "$here/generate-source-table.py" "$candidate" "$repo" "$out"
  check "$out/${candidate}Data.lean"
done
python3 -I "$here/generate-indexed-startup.py" PA1944L "$repo" "$out" --restricted
for source in "$out"/PA1944LRestrictedChunk[0-9][0-9].lean "$out/PA1944LRestrictedComplete.lean"; do
  check "$source"
done
for module in PA194CommonStartupRows PA194CommonStartup PA194CommonModelStartup; do
  check "$here/$module.lean"
done
for name in lca m4r; do
  rg -Fxq "'PA194CommonModelStartup.$name' depends on axioms: [propext, Classical.choice, Quot.sound]" \
    "$out/PA194CommonModelStartup.log"
done
printf '%s\n' "$LEAN_PATH" >"$out/leanpath.txt"
