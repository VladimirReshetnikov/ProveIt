#!/usr/bin/env bash
set -euo pipefail
ulimit -s unlimited
ulimit -c 0
here=$(cd -- "$(dirname -- "$0")" && pwd)
out=${1:?usage: check-ax-frame.sh FRESH_OUTPUT BODY_OUTPUT FETCH_OUTPUT AX_LOCAL_OUTPUT SCHEDULER_CORE_OUTPUT CONTROLLER_OUTPUT FRAME_OUTPUT}
body=${2:?missing BODY_OUTPUT}
fetch=${3:?missing FETCH_OUTPUT}
axlocal=${4:?missing AX_LOCAL_OUTPUT}
core=${5:?missing SCHEDULER_CORE_OUTPUT}
ctl=${6:?missing CONTROLLER_OUTPUT}
frame=${7:?missing FRAME_OUTPUT}
[[ ! -e "$out" ]] || { echo 'Output must be fresh' >&2; exit 2; }
[[ -f "$body/leanpath.txt" && -f "$fetch/leanpath.txt" && -f "$axlocal/PA194AX11HAXDispatch.olean" && -f "$core/PA194ControllerSchedulerCore.olean" && -f "$ctl/ConPACtlWords.olean" && -f "$frame/PA194SchedulerSourceFrame.olean" ]] || { echo 'Missing prerequisite output' >&2; exit 2; }
mkdir -p "$out"
out=$(cd -- "$out" && pwd)
for var in body fetch axlocal core ctl frame; do printf -v "$var" '%s' "$(cd -- "${!var}" && pwd)"; done
modules=(PA194AX11HAXSchedulerFields PA194AX11HAXFrame)
for m in "${modules[@]}"; do sha256sum "$here/$m.lean"; done > "$out/inputs.sha256"
sha256sum "$body/PA194AX11HBodyToFrame.olean" "$fetch/PA194AX11HDecodeScheduler.olean" "$axlocal/PA194AX11HAXDispatch.olean" "$core/PA194ControllerSchedulerCore.olean" "$ctl/ConPACtlWords.olean" "$frame/PA194SchedulerSourceFrame.olean" >> "$out/inputs.sha256"
base=$(python3 - "$frame" "$core" "$ctl" "$fetch" "$axlocal" "$body" <<'PYCODE'
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
echo 'PASS: candidate AX scheduler-frame command conditional on body row agreement.'
