#!/usr/bin/env bash
set -euo pipefail
base=Computability/BusyBeaver/Research/PA
package=$base/pa194-command-source
upstream=$base/jamesyc-upstream/pa196
task_dir=$(mktemp -d "${TMPDIR:-/dev/shm}/pa194-command-source.XXXXXXXX")
trap 'rm -rf "$task_dir"' EXIT
# Retain the fully checked AX builder's isolated objects for this composition.
python3 - "$base/pa194-ax-guard/check.sh" "$task_dir/ax.sh" <<'PY'
from pathlib import Path
import re,sys
s=Path(sys.argv[1]).read_text()
s,n=re.subn(r'^task_dir=\$\(mktemp[^\n]*\)\s*$', 'task_dir=$PA194_COMMAND_TASK_DIR', s, count=1, flags=re.M)
if n!=1: raise SystemExit('unexpected AX task directory declaration')
old="trap 'rm -rf \"$task_dir\"' EXIT"
if s.count(old)!=1: raise SystemExit('unexpected AX cleanup declaration')
Path(sys.argv[2]).write_text(s.replace(old,'',1))
PY
export PA194_COMMAND_TASK_DIR="$task_dir"
bash "$task_dir/ax.sh"
sha256sum -c "$package/upstream.sha256"
sha256sum -c "$base/pa194-shift-source/upstream.sha256"
export LEAN_PATH="$task_dir:$(lake env printenv LEAN_PATH)"
mkdir -p "$task_dir/PA196/Commands"
for mod in S36Drain CyclicDriver CyclicDeterminism CyclicInvariant NonexitCycle; do
 lean -M6000 -j1 -o "$task_dir/M6/Source/$mod.olean" "$upstream/M6/Source/$mod.lean"
done
lean -M6000 -j1 -o "$task_dir/PA196/Commands/Store.olean" "$upstream/PA196/Commands/Store.lean"
lean -M6000 -j1 -o "$task_dir/PA194AXReadable.olean" "$base/pa194-ax-guard/PA194AXReadable.lean"
for mod in PA194StackDecode PA194NIPBinding PA194S36Binding PA194S36Lift PA194NIPGuard PA194ShiftCommand; do
 lean -M6000 -j1 -o "$task_dir/$mod.olean" "$base/pa194-shift-source/$mod.lean"
done
for mod in PA194MPField PA194MPPush PA194MPCopy PA194MPCons PA194MPGuardSteps PA194MPGuard PA194MPStore PA194MPPrelude PA194MPSuccessPush PA194MPCommand; do
 lean -M6000 -j1 -o "$task_dir/$mod.olean" "$base/pa194-mp-source/$mod.lean"
done
for mod in PA194FetchPrefixBinding PA194FetchPrefix PA194FetchDecode PA194Fetch PA194Dispatch PA194FetchDispatch PA194CommandRegisters PA194CommandTransfer PA194FetchCommand PA194CommandRun; do
 lean -M6000 -j1 -o "$task_dir/$mod.olean" "$package/$mod.lean"
done
lean -M6000 -j1 "$package/PA194CommandEquiv.lean" | tee "$task_dir/axioms.log"
if rg -q 'sorryAx' "$task_dir/axioms.log"; then
 echo 'Unexpected sorryAx in command scheduler theorem' >&2
 exit 1
fi
