#!/usr/bin/env bash
set -euo pipefail
p=Computability/BusyBeaver/Research/PA/pa194/ipra/machine-code
stage=/dev/shm
base=$stage/pa194-fetch-coherent-full-v2
out=${1:?fresh output required}
mkdir "$out"
lake_path=$(lake env printenv LEAN_PATH)
core="$stage/pa194-compressed-controller-repo:$(paste -sd ':' "$p/compressed-controller-stages.txt")"
ulimit -s 65536
ulimit -c 0
LEAN_PATH="$out:$core:$lake_path" lean -j1 -M6000 -R "$p" -o "$out/PA194SourceSchedulerOrbit.olean" \
  "$p/PA194SourceSchedulerOrbit.lean" >"$out/PA194SourceSchedulerOrbit.log" 2>&1
export LEAN_PATH="$out:$stage/pa194-model-mp-packages:$stage/pa194-scheduler-dispatch-preserving-repo:$stage/pa194-compressed-controller-repo:$stage/pa194-scheduler-branches-open-repo:$stage/pa194-scheduler-decode-open-replay:$stage/pa194-decoder-native-replay:$stage/pa194-dispatch-replay:$base:$base/foundation-view:$core:$lake_path"
lean -j1 -M6000 -R "$p" -o "$out/PA194SchedulerSourceFrame.olean" "$p/PA194SchedulerSourceFrame.lean" >"$out/PA194SchedulerSourceFrame.log" 2>&1
if rg -q 'sorryAx|Lean.ofReduceBool' "$out/"*.log; then exit 1; fi
rg -Fq "'PA194SourceSchedulerOrbit.equivalent' depends on axioms:" "$out/PA194SourceSchedulerOrbit.log"
rg -Fq "'PA194SchedulerSourceFrame.equivalent_of_return' depends on axioms:" "$out/PA194SchedulerSourceFrame.log"
echo 'PASS: controller and scheduler agree given the returning-command contracts'
