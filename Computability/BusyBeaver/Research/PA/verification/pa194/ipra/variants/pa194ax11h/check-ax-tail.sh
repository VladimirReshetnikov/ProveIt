#!/usr/bin/env bash
set -euo pipefail
ulimit -s unlimited
ulimit -c 0
here=$(cd -- "$(dirname -- "$0")" && pwd)
out=${1:?usage: check-ax-tail.sh FRESH_OUTPUT PREP_OUTPUT COMPARISON_OUTPUT}
prep=${2:?usage: check-ax-tail.sh FRESH_OUTPUT PREP_OUTPUT COMPARISON_OUTPUT}
compare=${3:?usage: check-ax-tail.sh FRESH_OUTPUT PREP_OUTPUT COMPARISON_OUTPUT}
[[ ! -e "$out" ]] || { echo 'Output must be fresh' >&2; exit 2; }
[[ -f "$prep/leanpath.txt" && -f "$compare/leanpath.txt" ]] || { echo 'Missing prerequisite output or LEAN_PATH file' >&2; exit 2; }
mkdir -p "$out"
out=$(cd -- "$out" && pwd)
prep=$(cd -- "$prep" && pwd)
compare=$(cd -- "$compare" && pwd)
modules=(PA194AX11HZeroGuard PA194AX11HAXTail PA194AX11HAXTailValues)
for module in "${modules[@]}"; do sha256sum "$here/$module.lean"; done > "$out/inputs.sha256"
sha256sum "$prep/PA194AX11HThroughPrepValues.olean" "$compare/PA194AX11HCompareReturn.olean" >> "$out/inputs.sha256"
base=$(python3 - "$prep" "$compare" <<'PYCODE'
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
  lean -j1 -M4500 -R "$here" -o "$out/$module.olean" "$here/$module.lean" > "$out/$module.log" 2>&1 || { cat "$out/$module.log"; exit 1; }
  cat "$out/$module.log"
  if rg -q 'sorryAx|error:|Lean.ofReduceBool|declaration uses .sorry' "$out/$module.log"; then exit 1; fi
done
sha256sum -c "$out/inputs.sha256" >/dev/null
printf '%s\n' "$LEAN_PATH" > "$out/leanpath.txt"
echo 'PASS: exact AX11H AX fall-through to source dispatch.'
