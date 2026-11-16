#!/usr/bin/env bash
set -euo pipefail
ulimit -s unlimited
ulimit -c 0
here=$(cd -- "$(dirname -- "$0")" && pwd)
out=${1:?usage: check-initial-orbit.sh FRESH_OUTPUT SOURCE_ORBIT_OUTPUT SCHEDULER_FRAME_OUTPUT}
orbit=${2:?usage: check-initial-orbit.sh FRESH_OUTPUT SOURCE_ORBIT_OUTPUT SCHEDULER_FRAME_OUTPUT}
frame=${3:?usage: check-initial-orbit.sh FRESH_OUTPUT SOURCE_ORBIT_OUTPUT SCHEDULER_FRAME_OUTPUT}
[[ ! -e "$out" ]] || { echo 'Output must be fresh' >&2; exit 2; }
[[ -f "$orbit/leanpath.txt" && -f "$frame/PA194SchedulerSourceFrame.olean" ]] || { echo 'Missing source-orbit or scheduler-frame prerequisite' >&2; exit 2; }
mkdir -p "$out"
out=$(cd -- "$out" && pwd)
orbit=$(cd -- "$orbit" && pwd)
frame=$(cd -- "$frame" && pwd)
modules=(PA194AX11HInitialOrbit PA194AX11HDropOrbit)
for module in "${modules[@]}"; do sha256sum "$here/$module.lean"; done > "$out/inputs.sha256"
sha256sum "$orbit/PA194AX11HSourceOrbit.olean" "$frame/PA194SchedulerSourceFrame.olean" >> "$out/inputs.sha256"
export LEAN_PATH="$out:$frame:$(cat "$orbit/leanpath.txt")"
for module in "${modules[@]}"; do
  echo "Checking $module"
  lean -j1 -M4500 -R "$here" -o "$out/$module.olean" "$here/$module.lean" > "$out/$module.log" 2>&1 || { cat "$out/$module.log"; exit 1; }
  cat "$out/$module.log"
  if rg -q 'sorryAx|error:|Lean.ofReduceBool|declaration uses .sorry' "$out/$module.log"; then exit 1; fi
done
sha256sum -c "$out/inputs.sha256" >/dev/null
printf '%s\n' "$LEAN_PATH" > "$out/leanpath.txt"
echo 'PASS: initial source orbit, conditional on returning and halting command contracts.'
