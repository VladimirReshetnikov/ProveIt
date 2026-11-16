#!/usr/bin/env bash
set -euo pipefail
ulimit -s unlimited
ulimit -c 0
here=$(cd -- "$(dirname -- "$0")" && pwd)
out=${1:?usage: check-gate-frame.sh FRESH_OUTPUT GATE_WINDOW_OUTPUT COMPARISON_OUTPUT AX_TAIL_FRAME_OUTPUT PRIMARY_AX_OUTPUT}
gate=${2:?missing GATE_WINDOW_OUTPUT}
compare=${3:?missing COMPARISON_OUTPUT}
tail=${4:?missing AX_TAIL_FRAME_OUTPUT}
primary=${5:?missing PRIMARY_AX_OUTPUT}
[[ ! -e "$out" ]] || { echo 'Output must be fresh' >&2; exit 2; }
[[ -f "$tail/leanpath.txt" && -f "$gate/PA194AX11HGateBinding.olean" && -f "$compare/PA194AX11HCandidateDrain.olean" && -f "$primary/PA194ModelAXGate.olean" ]] || { echo 'Missing prerequisite output' >&2; exit 2; }
mkdir -p "$out"
out=$(cd -- "$out" && pwd)
gate=$(cd -- "$gate" && pwd)
compare=$(cd -- "$compare" && pwd)
tail=$(cd -- "$tail" && pwd)
primary=$(cd -- "$primary" && pwd)
modules=(PA194AX11HGateCopy PA194AX11HGateCompare PA194AX11HGateExact PA194AX11HGateToFrame)
for module in "${modules[@]}"; do sha256sum "$here/$module.lean"; done > "$out/inputs.sha256"
sha256sum "$gate/PA194AX11HGateBinding.olean" "$compare/PA194AX11HCandidateDrain.olean" "$primary/PA194ModelAXGate.olean" "$primary/PA194ModelAXCompare.olean" "$tail/PA194AX11HAXTailFrame.olean" >> "$out/inputs.sha256"
export LEAN_PATH="$out:$gate:$compare:$primary:$(cat "$tail/leanpath.txt")"
for module in "${modules[@]}"; do
  echo "Checking $module"
  lean -j1 -M4500 -R "$here" -o "$out/$module.olean" "$here/$module.lean" > "$out/$module.log" 2>&1 || { cat "$out/$module.log"; exit 1; }
  cat "$out/$module.log"
  if rg -q 'sorryAx|error:|Lean.ofReduceBool|declaration uses .sorry' "$out/$module.log"; then exit 1; fi
done
sha256sum -c "$out/inputs.sha256" >/dev/null
printf '%s\n' "$LEAN_PATH" > "$out/leanpath.txt"
echo 'PASS: candidate AX gate through exact next source frame.'
