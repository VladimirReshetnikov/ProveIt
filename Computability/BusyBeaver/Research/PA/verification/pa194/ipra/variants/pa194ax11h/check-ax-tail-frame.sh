#!/usr/bin/env bash
set -euo pipefail
ulimit -s unlimited
ulimit -c 0
here=$(cd -- "$(dirname -- "$0")" && pwd)
out=${1:?usage: check-ax-tail-frame.sh FRESH_OUTPUT AX_TAIL_OUTPUT}
tail_out=${2:?usage: check-ax-tail-frame.sh FRESH_OUTPUT AX_TAIL_OUTPUT}
[[ ! -e "$out" ]] || { echo 'Output must be fresh' >&2; exit 2; }
[[ -f "$tail_out/leanpath.txt" ]] || { echo 'Missing AX tail output' >&2; exit 2; }
mkdir -p "$out"
out=$(cd -- "$out" && pwd)
tail_out=$(cd -- "$tail_out" && pwd)
sha256sum "$here/PA194AX11HAXTailFrame.lean" "$tail_out/PA194AX11HAXTailValues.olean" > "$out/inputs.sha256"
export LEAN_PATH="$out:$(cat "$tail_out/leanpath.txt")"
lean -j1 -M4500 -R "$here" -o "$out/PA194AX11HAXTailFrame.olean" "$here/PA194AX11HAXTailFrame.lean" > "$out/PA194AX11HAXTailFrame.log" 2>&1 || { cat "$out/PA194AX11HAXTailFrame.log"; exit 1; }
cat "$out/PA194AX11HAXTailFrame.log"
if rg -q 'sorryAx|error:|Lean.ofReduceBool|declaration uses .sorry' "$out/PA194AX11HAXTailFrame.log"; then exit 1; fi
sha256sum -c "$out/inputs.sha256" >/dev/null
printf '%s\n' "$LEAN_PATH" > "$out/leanpath.txt"
echo 'PASS: AX tail returns the exact scheduler frame in positive time.'
