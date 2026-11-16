#!/usr/bin/env bash
set -euo pipefail
ulimit -s unlimited
ulimit -c 0

model=$(cd -- "${1:?checked radix source stage required}" && pwd)
out=${2:?fresh output directory required}
coefficient=${3:-5}
here=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
case $coefficient in
  5|6) ;;
  *) printf 'Expected coefficient 5 or 6\n' >&2; exit 2 ;;
esac
test -f "$model/PA194M${coefficient}Constructor.olean"
test ! -e "$out"
mkdir -p "$out"
out=$(cd -- "$out" && pwd)
export LEAN_PATH="$out:$model:$(cat "$model/leanpath.txt")"

modules=(PA194ProgramTransfer PA194ProgramCantorWalker PA194ProgramCantorPair PA194ProgramCons)
theorems=(PA194ProgramTransfer.transfer PA194ProgramCantorWalker.walk
  PA194ProgramCantorPair.pair PA194ProgramCons.execute)
if [[ $coefficient == 5 ]]; then
  modules+=(PA194M5Cons)
  theorems+=(PA194M5Cons.firstCons)
fi
for module in "${modules[@]}"; do
  log="$out/$module.log"
  if ! lean -j1 -M5000 -R "$here" -o "$out/$module.olean" "$here/$module.lean" > "$log" 2>&1; then
    cat "$log"
    exit 1
  fi
  cat "$log"
  if rg -q "error:|sorryAx|Lean.ofReduceBool|declaration uses 'sorry'" "$log"; then exit 1; fi
  printf 'PASS %s\n' "$module"
done

for pair in "${theorems[@]}"; do
  rg -Fxq "'$pair' depends on axioms: [propext, Classical.choice, Quot.sound]" "$out/${pair%%.*}.log"
done
if [[ $coefficient == 5 ]]; then
  rg -Fxq "'PA194M5Cons.rows' depends on axioms: [propext]" "$out/PA194M5Cons.log"
fi
sources=()
for module in "${modules[@]}"; do
  sources+=("$here/$module.lean")
done
sha256sum "${sources[@]}" "$here/check-cons.sh" "$out"/*.olean > "$out/sha256.txt"
printf '%s\n' "$LEAN_PATH" > "$out/leanpath.txt"
