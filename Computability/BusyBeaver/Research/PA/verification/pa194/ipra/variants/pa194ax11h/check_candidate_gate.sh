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
out=${1:?usage: check_candidate_gate.sh FRESH_OUTPUT CANDIDATE_OUTPUT}
candidate=${2:?usage: check_candidate_gate.sh FRESH_OUTPUT CANDIDATE_OUTPUT}
[[ ! -e "$out" ]] || { echo 'Output must be fresh' >&2; exit 2; }
[[ -f "$candidate/leanpath.txt" ]] || { echo 'Missing prerequisite candidate output' >&2; exit 2; }
mkdir -p "$out/generated"
out=$(cd -- "$out" && pwd)
candidate=$(cd -- "$candidate" && pwd)
python3 "$here/generate_gate_data.py" "$repo" "$out/generated"
cmp "$here/PA194AX11HGateData.lean" "$out/generated/PA194AX11HGateData.lean" || {
  echo 'Generated gate data differs from the checked-in source' >&2; exit 1;
}
modules=(PA194AX11HSharedRows PA194AX11HGateRows PA194AX11HGateBinding
  PA194AX11HGateWindow PA194AX11HGateInterval PA194AX11HGateRun
  PA194AX11HGateData PA194AX11HGateNext PA194AX11HGateClosure)
for module in "${modules[@]}"; do
  [[ -f "$here/$module.lean" ]] || { echo "Missing source: $module" >&2; exit 1; }
  sha256sum "$here/$module.lean"
done > "$out/inputs.sha256"
sha256sum "$here/generate_gate_data.py" "$candidate/PA194AX11HSource.olean" \
  "$candidate/PA194AX11HPushOriginal.olean" >> "$out/inputs.sha256"
base=$(python3 - "$candidate" <<'PYCODE'
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
  lean -j1 -M4500 -R "$here" -o "$out/$module.olean" "$here/$module.lean" > "$out/$module.log" 2>&1 || { cat "$out/$module.log"; exit 1; }
  cat "$out/$module.log"
  if rg -q 'sorryAx|error:|Lean.ofReduceBool|declaration uses .sorry' "$out/$module.log"; then exit 1; fi
done
sha256sum -c "$out/inputs.sha256" >/dev/null
printf '%s\n' "$LEAN_PATH" > "$out/leanpath.txt"
echo 'PASS: AX11H local AX-gate source window.'
