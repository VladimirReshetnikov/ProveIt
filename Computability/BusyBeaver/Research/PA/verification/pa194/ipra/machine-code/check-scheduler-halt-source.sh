#!/usr/bin/env bash
set -euo pipefail
p=Computability/BusyBeaver/Research/PA/verification/pa194/ipra/machine-code
out=${1:?fresh output required}
mkdir "$out"
stage=/dev/shm
base=$stage/pa194-fetch-coherent-full-v2
lake_path=$(lake env printenv LEAN_PATH)
export LEAN_PATH="$out:$stage/pa194-scheduler-branches-open-repo:$stage/pa194-scheduler-decode-open-replay:$stage/pa194-decoder-native-replay:$stage/pa194-dispatch-replay:$base:$base/foundation-view:/tmp/current14-standard-fresh-build-20261104/lib:/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib:$lake_path"
ulimit -s 65536
ulimit -c 0
for m in PA194SchedulerDispatchOpen PA194SchedulerBranchesOpen PA194ShiftModelHalt PA194SchedulerHaltSource; do
  result=0
  lean -j1 -M6000 -R "$p" -o "$out/$m.olean" "$p/$m.lean" >"$out/$m.log" 2>&1 || result=$?
  cat "$out/$m.log"
  test "$result" = 0
  ! rg -q 'sorryAx|Lean.ofReduceBool' "$out/$m.log"
done
rg -Fq "'PA194SchedulerHaltSource.haltFromRoot' depends on axioms:" "$out/PA194SchedulerHaltSource.log"
