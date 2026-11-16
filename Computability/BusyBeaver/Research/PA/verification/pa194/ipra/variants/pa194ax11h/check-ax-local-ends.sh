#!/usr/bin/env bash
set -euo pipefail
ulimit -s unlimited
ulimit -c 0
here=$(cd -- "$(dirname -- "$0")" && pwd)
out=${1:?usage: check-ax-local-ends.sh FRESH_OUTPUT GATE_DECODED_OUTPUT MP_COMMAND_OUTPUT}
gate=${2:?missing GATE_DECODED_OUTPUT}
mp=${3:?missing MP_COMMAND_OUTPUT}
[[ ! -e "$out" ]] || { echo 'Output must be fresh' >&2; exit 2; }
[[ -f "$gate/leanpath.txt" && -f "$mp/leanpath.txt" ]] || { echo 'Missing prerequisite output' >&2; exit 2; }
mkdir -p "$out"
out=$(cd -- "$out" && pwd)
gate=$(cd -- "$gate" && pwd)
mp=$(cd -- "$mp" && pwd)
modules=(PA194AX11HGateMeaning PA194AX11HAXDispatch)
for module in "${modules[@]}"; do sha256sum "$here/$module.lean"; done > "$out/inputs.sha256"
sha256sum "$gate/PA194AX11HGateDecoded.olean" "$mp/PA194AX11HMPDispatch.olean" >> "$out/inputs.sha256"
base=$(python3 - "$gate" "$mp" <<'PYCODE'
import sys
seen = set()
paths = []
for directory in sys.argv[1:]:
    for path in [directory] + open(directory + '/leanpath.txt', encoding='utf-8').read().strip().split(':'):
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
echo 'PASS: AX opcode dispatch and gate output meaning.'
