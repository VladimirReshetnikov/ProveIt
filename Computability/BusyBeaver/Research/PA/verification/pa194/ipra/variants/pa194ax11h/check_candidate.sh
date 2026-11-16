#!/usr/bin/env bash
set -euo pipefail
ulimit -s unlimited
ulimit -c 0
here=$(cd -- "$(dirname -- "$0")" && pwd)
repo=$here
while [[ ! -f "$repo/lakefile.toml" ]]; do
  parent=$(dirname -- "$repo")
  [[ "$parent" != "$repo" ]] || { echo 'Cannot locate repository root' >&2; exit 2; }
  repo=$parent
done
out=${1:?usage: check_candidate.sh FRESH_OUTPUT BASE_LEAN_PATH_FILE}
pathfile=${2:?usage: check_candidate.sh FRESH_OUTPUT BASE_LEAN_PATH_FILE}
[[ ! -e "$out" ]] || { echo 'Output must be fresh' >&2; exit 2; }
[[ -f "$pathfile" ]] || { echo 'Base LEAN_PATH file does not exist' >&2; exit 2; }
mkdir -p "$out/generated"
out=$(cd -- "$out" && pwd)
for generator in generate_push_rows.py generate_source.py generate_field_rows.py; do
  python3 "$here/$generator" "$repo" "$out/generated"
done
for module in PA194AX11HPushRows PA194AX11HSource PA194AX11HFieldRows; do
  cmp "$here/$module.lean" "$out/generated/$module.lean" || {
    echo "Generated $module differs from the checked-in source" >&2; exit 1;
  }
done
modules=(
  PA194AX11HRelocation PA194AX11HPushRows PA194AX11HPushSemantics
  PA194AX11HPushCongruence PA194AX11HPrimaryPush PA194AX11HSource
  PA194AX11HSourcePush PA194AX11HPushNext PA194AX11HPushAdvance
  PA194AX11HFieldRows PA194AX11HFieldSemantics PA194AX11HFieldSource
  PA194AX11HFieldNext PA194AX11HFieldAdvance PA194AX11HPushPaused
  PA194AX11HFieldPaused PA194AX11HPushAlignedDef PA194AX11HPushIteration
  PA194AX11HPushIterationExtra PA194AX11HPushOriginal PA194AX11HPushOriginalReach
  PA194PausedReach PA194PausedSites PA194PausedDrain PA194PausedTransfer
  PA194PausedPair PA194PausedPush PA194PausedFirstHit PA194FirstActualPush
  PA194AX11HPushExact
)
for module in "${modules[@]}"; do
  [[ -f "$here/$module.lean" ]] || { echo "Missing source: $module" >&2; exit 1; }
done
for module in "${modules[@]}"; do sha256sum "$here/$module.lean"; done > "$out/inputs.sha256"
for generator in generate_push_rows.py generate_source.py generate_field_rows.py; do sha256sum "$here/$generator"; done >> "$out/inputs.sha256"
export LEAN_PATH="$out:$(cat "$pathfile")"
for module in "${modules[@]}"; do
  echo "Checking $module"
  lean -j1 -M6000 -R "$here" -o "$out/$module.olean" "$here/$module.lean" > "$out/$module.log" 2>&1 || { cat "$out/$module.log"; exit 1; }
  cat "$out/$module.log"
  if rg -q 'sorryAx|error:|Lean.ofReduceBool|declaration uses .sorry' "$out/$module.log"; then exit 1; fi
done
sha256sum -c "$out/inputs.sha256" >/dev/null
printf '%s\n' "$LEAN_PATH" > "$out/leanpath.txt"
echo 'PASS: exact AX11H source push and prerequisite modules.'
