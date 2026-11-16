#!/usr/bin/env bash
set -euo pipefail
ulimit -s unlimited
ulimit -c 0

base=$(cd -- "${1:?checked shared AX11H controller stage required}" && pwd)
out=${2:?fresh output directory required}
here=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
repo=$(git -C "$here" rev-parse --show-toplevel)
test ! -e "$out"
mkdir -p "$out"
out=$(cd -- "$out" && pwd)
export LEAN_PATH="$out:$base:$(cat "$base/leanpath.txt")"

python3 -I "$here/../generate-source-table.py" PA194GS "$repo" "$out"
python3 -I "$here/../generate-indexed-startup.py" PA194GS "$repo" "$out"

check() {
  local source=$1 module=${1##*/} log
  module=${module%.lean}
  log="$out/$module.log"
  if ! lean -j1 -M5350 -R "$(dirname -- "$source")" -o "$out/$module.olean" "$source" >"$log" 2>&1; then
    cat "$log"
    return 1
  fi
  cat "$log"
  if rg -q "error[:(]|sorryAx|Lean.ofReduceBool|declaration uses 'sorry'" "$log"; then return 1; fi
}

check "$out/PA194GSData.lean"
for suffix in Rows BoxAgreement Checks Numerical; do
  check "$here/PA194GS$suffix.lean"
done
for source in "$out"/PA194GSStartupChunk*.lean "$out/PA194GSStartupComplete.lean"; do
  check "$source"
done
for suffix in ModelStartup Controller; do
  check "$here/PA194GS$suffix.lean"
done
for theorem in startup_root halt_iff_site10; do
  rg -Fxq "'PA194GSController.$theorem' depends on axioms: [propext, Classical.choice, Quot.sound]" \
    "$out/PA194GSController.log"
done
printf '%s\n' "$LEAN_PATH" >"$out/leanpath.txt"
