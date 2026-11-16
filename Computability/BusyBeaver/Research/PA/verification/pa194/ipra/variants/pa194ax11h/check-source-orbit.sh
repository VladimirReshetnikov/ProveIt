#!/usr/bin/env bash
set -euo pipefail
ulimit -s unlimited
ulimit -c 0
here=$(cd -- "$(dirname -- "$0")" && pwd)
out=${1:?usage: check-source-orbit.sh FRESH_OUTPUT CANDIDATE_OUTPUT}
candidate=${2:?usage: check-source-orbit.sh FRESH_OUTPUT CANDIDATE_OUTPUT}
[[ ! -e "$out" ]] || { echo 'Output must be fresh' >&2; exit 2; }
[[ -f "$candidate/leanpath.txt" ]] || { echo 'Missing candidate output' >&2; exit 2; }
mkdir -p "$out"
out=$(cd -- "$out" && pwd)
candidate=$(cd -- "$candidate" && pwd)
sha256sum "$here/PA194AX11HSentinel.lean" "$here/PA194AX11HSourceOrbit.lean" \
  "$candidate/PA194AX11HSource.olean" > "$out/inputs.sha256"
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
for module in PA194AX11HSentinel PA194AX11HSourceOrbit; do
  echo "Checking $module"
  lean -j1 -M4500 -R "$here" -o "$out/$module.olean" "$here/$module.lean" > "$out/$module.log" 2>&1 || { cat "$out/$module.log"; exit 1; }
  cat "$out/$module.log"
  if rg -q 'sorryAx|error:|Lean.ofReduceBool|declaration uses .sorry' "$out/$module.log"; then exit 1; fi
done
sha256sum -c "$out/inputs.sha256" >/dev/null
printf '%s\n' "$LEAN_PATH" > "$out/leanpath.txt"
echo 'PASS: conditional AX11H site-10/source scheduler orbit equivalence.'
