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
out=${1:?usage: check_candidate_prep.sh FRESH_OUTPUT DOUBLE_PUSH_OUTPUT}
double=${2:?usage: check_candidate_prep.sh FRESH_OUTPUT DOUBLE_PUSH_OUTPUT}
[[ ! -e "$out" ]] || { echo 'Output must be fresh' >&2; exit 2; }
[[ -f "$double/leanpath.txt" ]] || { echo 'Missing prerequisite double-push output' >&2; exit 2; }
mkdir -p "$out/generated"
out=$(cd -- "$out" && pwd)
double=$(cd -- "$double" && pwd)
python3 "$here/generate_prep_rows.py" "$repo" "$out/generated"
cmp "$here/PA194AX11HPrepRows.lean" "$out/generated/PA194AX11HPrepRows.lean" || {
  echo 'Generated preparation rows differ from the checked-in source' >&2; exit 1;
}
modules=(PA194AX11HPrepRows PA194AX11HPrepSemantics PA194AX11HPrepSource
  PA194AX11HPrepNext PA194AX11HPrepAdvance PA194PausedCopy PA194PausedImp
  PA194AX11HPrepPaused PA194AX11HPrepAlignedDef PA194AX11HPrepIteration
  PA194AX11HPrepIterationExtra PA194AX11HPrepOriginal PA194AX11HPrepOriginalReach
  PA194PausedPrep PA194AX11HPrepExact PA194AX11HThroughPrep PA194AX11HThroughPrepValues)
for module in "${modules[@]}"; do
  [[ -f "$here/$module.lean" ]] || { echo "Missing source: $module" >&2; exit 1; }
  sha256sum "$here/$module.lean"
done > "$out/inputs.sha256"
sha256sum "$here/generate_prep_rows.py" "$double/PA194AX11HDoublePushField.olean" >> "$out/inputs.sha256"
base=$(python3 - "$double" <<'PYCODE'
import sys
seen = set()
paths = []
for path in [sys.argv[1]] + open(sys.argv[1] + '/leanpath.txt', encoding='utf-8').read().strip().split(':'):
    if path and path not in seen:
        seen.add(path)
        paths.append(path)
print(':'.join(paths))
PYCODE
)
export LEAN_PATH="$out:$base"
for module in "${modules[@]}"; do
  echo "Checking $module"
  lean -j1 -M6000 -R "$here" -o "$out/$module.olean" "$here/$module.lean" > "$out/$module.log" 2>&1 || { cat "$out/$module.log"; exit 1; }
  cat "$out/$module.log"
  if rg -q 'sorryAx|error:|Lean.ofReduceBool|declaration uses .sorry' "$out/$module.log"; then exit 1; fi
done
sha256sum -c "$out/inputs.sha256" >/dev/null
printf '%s\n' "$LEAN_PATH" > "$out/leanpath.txt"
echo 'PASS: exact AX11H source execution through comparison preparation.'
