#!/usr/bin/env bash
set -euo pipefail
ulimit -s unlimited
ulimit -c 0
here=$(cd -- "$(dirname -- "$0")" && pwd)
out=${1:?usage: check.sh FRESH_OUTPUT GATE_WINDOW_OUTPUT COMPARISON_OUTPUT AX_LOCAL_ENDS_OUTPUT PRIMARY_AX_OUTPUT}
gate=${2:?missing GATE_WINDOW_OUTPUT}
compare=${3:?missing COMPARISON_OUTPUT}
axlocal=${4:?missing AX_LOCAL_ENDS_OUTPUT}
primary=${5:?missing PRIMARY_AX_OUTPUT}
[[ ! -e "$out" ]] || { echo 'Output must be fresh' >&2; exit 2; }
[[ -f "$gate/PA194AX11HGateBinding.olean" && -f "$compare/PA194AX11HCandidateDrain.olean" && -f "$axlocal/leanpath.txt" && -f "$primary/PA194ModelAXBound.olean" ]] || { echo 'Missing prerequisite output' >&2; exit 2; }
mkdir -p "$out"
out=$(cd -- "$out" && pwd)
for var in gate compare axlocal primary; do printf -v "$var" '%s' "$(cd -- "${!var}" && pwd)"; done
modules=(PA194AX11HPlanReduction PA194AX11HBodyCopy PA194AX11HWindowDrain PA194AX11HWindowTransfer PA194AX11HWindowPair PA194AX11HWindowPush PA194AX11HBodyWindow PA194AX11HWindowWalkerRound PA194AX11HWindowWalkerLoop PA194AX11HWindowReader PA194AX11HWindowReads PA194AX11HWindowCons PA194AX11HWindowConsExecute PA194AX11HBodyAll PA194AX11HBodyToFrame)
for m in "${modules[@]}"; do sha256sum "$here/$m.lean"; done > "$out/inputs.sha256"
sha256sum "$gate/PA194AX11HGateBinding.olean" "$compare/PA194AX11HCandidateDrain.olean" "$axlocal/PA194AX11HGateMeaning.olean" "$primary/PA194ModelAXBound.olean" "$primary/PA194AXModelValues.olean" >> "$out/inputs.sha256"
base=$(python3 - "$gate" "$compare" "$axlocal" "$primary" <<'PYCODE'
import sys
from pathlib import Path
seen=set(); paths=[]
for root in sys.argv[1:]:
    f=Path(root,'leanpath.txt')
    for p in [root] + (f.read_text().strip().split(':') if f.exists() else []):
        if p and p not in seen: seen.add(p); paths.append(p)
print(':'.join(paths))
PYCODE
)
export LEAN_PATH="$out:$base"
for m in "${modules[@]}"; do
  echo "Checking $m"
  lean -j1 -M5000 -R "$here" -o "$out/$m.olean" "$here/$m.lean" > "$out/$m.log" 2>&1 || { cat "$out/$m.log"; exit 1; }
  cat "$out/$m.log"
  if rg -q 'sorryAx|error:|Lean.ofReduceBool|declaration uses .sorry' "$out/$m.log"; then exit 1; fi
done
sha256sum -c "$out/inputs.sha256" >/dev/null
printf '%s\n' "$LEAN_PATH" > "$out/leanpath.txt"
echo 'PASS: candidate AX body to next source frame, conditional on body row agreement.'
