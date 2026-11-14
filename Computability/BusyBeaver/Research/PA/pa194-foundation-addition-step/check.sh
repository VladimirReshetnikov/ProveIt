#!/usr/bin/env bash
set -euo pipefail
: "${IPRA_FOUNDATION_OVERLAY:?Set IPRA_FOUNDATION_OVERLAY to the matching audited Lean 4.32 Foundation object directory}"
base=Computability/BusyBeaver/Research/PA
package=$base/pa194-foundation-addition-step
task_dir=$(mktemp -d "${TMPDIR:-/dev/shm}/pa194-foundation-addition-step.XXXXXXXX")
trap 'rm -rf "$task_dir"' EXIT
python3 - "$base/pa194-foundation-addition-zero/check.sh" "$task_dir/foundation-addition-step-prerequisites.sh" <<'PY'
from pathlib import Path
import re,sys
s=Path(sys.argv[1]).read_text()
s,n=re.subn(r'^task_dir=\$\(mktemp[^\n]*\)\s*$', 'task_dir=$PA194_FOUNDATION_ADDITION_STEP_TASK_DIR', s, count=1, flags=re.M)
if n != 1: raise SystemExit('unexpected zero addition task directory declaration')
old="trap 'rm -rf \"$task_dir\"' EXIT"
if s.count(old) != 1: raise SystemExit('unexpected zero addition cleanup declaration')
Path(sys.argv[2]).write_text(s.replace(old,'',1))
PY
export PA194_FOUNDATION_ADDITION_STEP_TASK_DIR="$task_dir"
bash -n "$task_dir/foundation-addition-step-prerequisites.sh"
bash "$task_dir/foundation-addition-step-prerequisites.sh"
sha256sum -c "$package/upstream.sha256"
export LEAN_PATH="$task_dir:$IPRA_FOUNDATION_OVERLAY:$(lake env printenv LEAN_PATH)"
# The addition-frame proof uses the previously checked successor derivation.
for suf in ClosureExtremaLogic ClosureTrace ClosureExtrema Closure Derivation; do
  mod="PA194FoundationOrdinalSuccessor$suf"
  lean -M6000 -j1 -o "$task_dir/$mod.olean" "$base/pa194-foundation-successor/$mod.lean" | tee -a "$task_dir/addition-step-axioms.log"
done
for suf in GraphOperations GraphOutputExtension OrdinalGraphOrder GraphFreshInput GraphDomainExtension GraphRangeExtension GraphFunctionalExtension AdditionRecurrence AdditionRecurrenceExtension AdditionFrame AdditionStepExistence AdditionStepWithZero AdditionGivenZero AdditionPrefixPayload AdditionPrefixStep AdditionStepNumeric; do
  mod="PA194Foundation$suf"
  lean -M6000 -j1 -o "$task_dir/$mod.olean" "$package/$mod.lean" | tee -a "$task_dir/addition-step-axioms.log"
done
if rg -q 'sorryAx' "$task_dir/addition-step-axioms.log"; then
  echo 'Unexpected sorryAx in addition step theorem dependencies' >&2
  exit 1
fi
