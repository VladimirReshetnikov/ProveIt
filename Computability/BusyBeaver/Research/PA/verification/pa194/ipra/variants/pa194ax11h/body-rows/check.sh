#!/usr/bin/env bash
set -euo pipefail
ulimit -s unlimited
ulimit -c 0
here=$(cd -- "$(dirname -- "$0")" && pwd)
out=${1:?usage: check.sh FRESH_OUTPUT BODY_PROOF_OUTPUT GATE_WINDOW_OUTPUT}
body=${2:?missing BODY_PROOF_OUTPUT}
gate=${3:?missing GATE_WINDOW_OUTPUT}
[[ ! -e "$out" ]] || { echo 'Output must be fresh' >&2; exit 2; }
[[ -f "$body/leanpath.txt" && -f "$body/PA194AX11HBodyCopy.olean" && -f "$gate/PA194AX11HGateBinding.olean" ]] || { echo 'Missing prerequisite output' >&2; exit 2; }
mkdir -p "$out/sources"
out=$(cd -- "$out" && pwd)
body=$(cd -- "$body" && pwd)
gate=$(cd -- "$gate" && pwd)
sha256sum "$here/generate.py" "$here/PA194AX11HBodyRowCommon.lean" "$body/PA194AX11HBodyCopy.olean" "$gate/PA194AX11HGateBinding.olean" > "$out/inputs.sha256"
python3 "$here/generate.py" "$out/sources"
cp "$here/PA194AX11HBodyRowCommon.lean" "$out/sources/"
sha256sum "$out/sources/"*.lean > "$out/generated.sha256"
export LEAN_PATH="$out:$gate:$(cat "$body/leanpath.txt")"
modules=(PA194AX11HBodyRowCommon)
for i in $(seq 0 27); do modules+=("$(printf 'PA194AX11HBodyRows%03d' "$i")"); done
modules+=(PA194AX11HBodyRowsAll)
for m in "${modules[@]}"; do
  echo "Checking $m"
  lean -j1 -M5000 -R "$out/sources" -o "$out/$m.olean" "$out/sources/$m.lean" > "$out/$m.log" 2>&1 || { cat "$out/$m.log"; exit 1; }
  cat "$out/$m.log"
  if rg -q 'sorryAx|error:|Lean.ofReduceBool|declaration uses .sorry' "$out/$m.log"; then exit 1; fi
done
sha256sum -c "$out/inputs.sha256" >/dev/null
sha256sum -c "$out/generated.sha256" >/dev/null
printf '%s\n' "$LEAN_PATH" > "$out/leanpath.txt"
echo 'PASS: all 3,469 AX body source rows match the primary trie.'
