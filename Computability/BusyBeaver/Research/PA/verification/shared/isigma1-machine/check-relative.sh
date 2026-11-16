#!/usr/bin/env bash
set -euo pipefail
ulimit -s unlimited
ulimit -c 0

base=$(cd -- "${1:?checked model or native stage required}" && pwd)
out=${2:?output directory required}
here=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
mkdir -p "$out"
out=$(cd -- "$out" && pwd)
export LEAN_PATH="$out:$(cat "$base/leanpath.txt")"

for module in ConPAISigma1Relative ConPAMachineRelative; do
  log="$out/$module.log"
  if ! lean -j1 -M5500 -R "$here" -o "$out/$module.olean" "$here/$module.lean" >"$log" 2>&1; then
    cat "$log"
    exit 1
  fi
  cat "$log"
  if rg -q "error:|sorryAx|Lean.ofReduceBool|declaration uses 'sorry'" "$log"; then exit 1; fi
done
rg -Fxq "'ConPA.MachineRelative.consistency_iff' depends on axioms: [propext, Classical.choice, Quot.sound]" \
  "$out/ConPAMachineRelative.log"
printf '%s\n' "$LEAN_PATH" >"$out/leanpath.txt"
