#!/usr/bin/env bash
set -euo pipefail
ulimit -s unlimited
ulimit -c 0

candidate=${1:?candidate (PA194LCA or PA194M4R) required}
case "$candidate" in
  PA194LCA | PA194M4R) ;;
  *) printf 'Unknown candidate %s\n' "$candidate" >&2; exit 2 ;;
esac
base=$(cd -- "${2:?checked common startup stage required}" && pwd)
out=${3:?output directory required}
here=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
dir="$here/${candidate,,}"
test -s "$base/PA194CommonModelStartup.olean"
mkdir -p "$out"
out=$(cd -- "$out" && pwd)
export LEAN_PATH="$out:$(cat "$base/leanpath.txt")"

for stage in Rows Checks Physical BoxAgreement ModelStartup Controller Initializer Native; do
  module=$candidate$stage
  log="$out/$module.log"
  if ! lean -j1 -M5350 -R "$dir" -o "$out/$module.olean" "$dir/$module.lean" >"$log" 2>&1; then
    cat "$log"
    exit 1
  fi
  cat "$log"
  if rg -q "error:|sorryAx|Lean.ofReduceBool|declaration uses 'sorry'" "$log"; then exit 1; fi
done
rg -Fxq "'${candidate}Native.consistency_iff_literal_nonhalt' depends on axioms: [propext, Classical.choice, Quot.sound]" "$out/${candidate}Native.log"
printf '%s\n' "$LEAN_PATH" >"$out/leanpath.txt"
