#!/usr/bin/env bash
set -euo pipefail
ulimit -s unlimited
ulimit -c 0
here=$(cd -- "$(dirname -- "$0")" && pwd)
out=${1:?usage: check-gate-decoded.sh FRESH_OUTPUT GATE_FRAME_OUTPUT}
gate=${2:?usage: check-gate-decoded.sh FRESH_OUTPUT GATE_FRAME_OUTPUT}
[[ ! -e "$out" ]] || { echo 'Output must be fresh' >&2; exit 2; }
[[ -f "$gate/leanpath.txt" ]] || { echo 'Missing gate-frame output' >&2; exit 2; }
mkdir -p "$out"
out=$(cd -- "$out" && pwd)
gate=$(cd -- "$gate" && pwd)
sha256sum "$here/PA194AX11HGateDecoded.lean" "$gate/PA194AX11HGateToFrame.olean" > "$out/inputs.sha256"
export LEAN_PATH="$out:$(cat "$gate/leanpath.txt")"
lean -j1 -M4500 -R "$here" -o "$out/PA194AX11HGateDecoded.olean" "$here/PA194AX11HGateDecoded.lean" > "$out/PA194AX11HGateDecoded.log" 2>&1 || { cat "$out/PA194AX11HGateDecoded.log"; exit 1; }
cat "$out/PA194AX11HGateDecoded.log"
if rg -q 'sorryAx|error:|Lean.ofReduceBool|declaration uses .sorry' "$out/PA194AX11HGateDecoded.log"; then exit 1; fi
sha256sum -c "$out/inputs.sha256" >/dev/null
printf '%s\n' "$LEAN_PATH" > "$out/leanpath.txt"
echo 'PASS: candidate AX gate with arbitrary stream decoding.'
