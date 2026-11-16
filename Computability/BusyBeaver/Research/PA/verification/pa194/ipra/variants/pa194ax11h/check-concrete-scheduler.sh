#!/usr/bin/env bash
set -euo pipefail
ulimit -s unlimited
ulimit -c 0
here=$(cd -- "$(dirname -- "$0")" && pwd)
out=${1:?usage: check-concrete-scheduler.sh FRESH_OUTPUT INITIAL_ORBIT_OUTPUT SCHEDULER_CORE_OUTPUT COMMAND_CONTROLLER_OUTPUT}
orbit=${2:?missing INITIAL_ORBIT_OUTPUT}
core=${3:?missing SCHEDULER_CORE_OUTPUT}
ctl=${4:?missing COMMAND_CONTROLLER_OUTPUT}
[[ ! -e "$out" ]] || { echo 'Output must be fresh' >&2; exit 2; }
[[ -f "$orbit/leanpath.txt" && -f "$core/PA194ControllerSchedulerCore.olean" && -f "$ctl/ConPACtlWords.olean" ]] || { echo 'Missing prerequisite output' >&2; exit 2; }
mkdir -p "$out"
out=$(cd -- "$out" && pwd)
orbit=$(cd -- "$orbit" && pwd)
core=$(cd -- "$core" && pwd)
ctl=$(cd -- "$ctl" && pwd)
sha256sum "$here/PA194AX11HConcreteScheduler.lean" "$orbit/PA194AX11HDropOrbit.olean" "$core/PA194ControllerSchedulerCore.olean" "$ctl/ConPACtlWords.olean" > "$out/inputs.sha256"
export LEAN_PATH="$out:$core:$ctl:$(cat "$orbit/leanpath.txt")"
lean -j1 -M4500 -R "$here" -o "$out/PA194AX11HConcreteScheduler.olean" "$here/PA194AX11HConcreteScheduler.lean" > "$out/PA194AX11HConcreteScheduler.log" 2>&1 || { cat "$out/PA194AX11HConcreteScheduler.log"; exit 1; }
cat "$out/PA194AX11HConcreteScheduler.log"
if rg -q 'sorryAx|error:|Lean.ofReduceBool|declaration uses .sorry' "$out/PA194AX11HConcreteScheduler.log"; then exit 1; fi
sha256sum -c "$out/inputs.sha256" >/dev/null
printf '%s\n' "$LEAN_PATH" > "$out/leanpath.txt"
echo 'PASS: candidate site 10 versus concrete AX11H scheduler, conditional on command contracts.'
