#!/usr/bin/env bash
set -euo pipefail
ulimit -s unlimited
ulimit -c 0

base=$(cd -- "${1:?checked AX11H controller stage required}" && pwd)
out=${2:?fresh output directory required}
here=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
repo=$(git -C "$here" rev-parse --show-toplevel)
test ! -e "$out"
mkdir -p "$out"
out=$(cd -- "$out" && pwd)
export LEAN_PATH="$out:$base:$(cat "$base/leanpath.txt")"

candidate=PA194LCAX11H
python3 -I "$here/../generate-source-table.py" "$candidate" "$repo" "$out"
python3 -I "$here/../generate-indexed-startup.py" "$candidate" "$repo" "$out"

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
  printf 'PASS %s\n' "$module"
}

check "$out/${candidate}Data.lean"
for suffix in Rows BoxAgreement Checks Numerical; do
  check "$here/$candidate$suffix.lean"
done
for source in "$out"/"${candidate}StartupChunk"*.lean "$out/${candidate}StartupComplete.lean"; do
  check "$source"
done
for suffix in ModelStartup Initializer Controller; do
  check "$here/$candidate$suffix.lean"
done
for theorem in Initializer.startup_root Controller.halt_iff_site10; do
  rg -Fxq "'$candidate$theorem' depends on axioms: [propext, Classical.choice, Quot.sound]" \
    "$out/$candidate${theorem%%.*}.log"
done
printf '%s\n' "$LEAN_PATH" >"$out/leanpath.txt"
