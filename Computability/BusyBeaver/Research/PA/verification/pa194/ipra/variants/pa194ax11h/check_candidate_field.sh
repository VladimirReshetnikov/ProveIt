#!/usr/bin/env bash
set -euo pipefail
ulimit -s unlimited
ulimit -c 0
here=$(cd -- "$(dirname -- "$0")" && pwd)
out=${1:?usage: check_candidate_field.sh FRESH_OUTPUT CANDIDATE_OUTPUT PRIMARY_FIELD_OUTPUT}
candidate=${2:?usage: check_candidate_field.sh FRESH_OUTPUT CANDIDATE_OUTPUT PRIMARY_FIELD_OUTPUT}
field=${3:?usage: check_candidate_field.sh FRESH_OUTPUT CANDIDATE_OUTPUT PRIMARY_FIELD_OUTPUT}
[[ ! -e "$out" ]] || { echo 'Output must be fresh' >&2; exit 2; }
[[ -f "$candidate/leanpath.txt" && -f "$field/leanpath.txt" ]] || { echo 'Missing prerequisite output or LEAN_PATH file' >&2; exit 2; }
mkdir -p "$out"
out=$(cd -- "$out" && pwd)
candidate=$(cd -- "$candidate" && pwd)
field=$(cd -- "$field" && pwd)
modules=(PA194AX11HFieldAlignedDef PA194AX11HFieldIteration PA194AX11HFieldIterationExtra
  PA194AX11HFieldOriginal PA194AX11HFieldOriginalReach PA194AX11HFieldExact PA194AX11HPushField PA194AX11HPushFieldValues)
for module in "${modules[@]}"; do
  [[ -f "$here/$module.lean" ]] || { echo "Missing source: $module" >&2; exit 1; }
  sha256sum "$here/$module.lean"
done > "$out/inputs.sha256"
sha256sum "$candidate/PA194AX11HPushExact.olean" "$candidate/PA194AX11HFieldPaused.olean" \
  "$candidate/PA194AX11HFieldAdvance.olean" "$field/PA194FirstActualField.olean" >> "$out/inputs.sha256"
base=$(python3 - "$candidate" "$field" <<'PYCODE'
import sys
seen = set()
paths = []
for path in (sys.argv[1], sys.argv[2]):
    if path not in seen:
        seen.add(path)
        paths.append(path)
for directory in (sys.argv[1], sys.argv[2]):
    with open(directory + '/leanpath.txt', encoding='utf-8') as f:
        for path in f.read().strip().split(':'):
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
echo 'PASS: exact AX11H source field and composed push/field output.'
