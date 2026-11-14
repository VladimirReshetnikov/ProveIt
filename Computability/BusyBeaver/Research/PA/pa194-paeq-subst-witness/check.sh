#!/usr/bin/env bash
set -euo pipefail
: "${IPRA_FOUNDATION_OVERLAY:?Set IPRA_FOUNDATION_OVERLAY to the audited Foundation object directory}"
: "${IPRA_LEAN_OVERLAY:?Set IPRA_LEAN_OVERLAY to the audited project object directory}"
base=Computability/BusyBeaver/Research/PA
root=$(mktemp -d "${TMPDIR:-/dev/shm}/pa194-paeq-subst-witness.XXXXXXXX")
trap 'rm -rf "$root"' EXIT
for dir in pa194-paeq-term-blueprint pa194-paeq-formula pa194-paeq-term-witness pa194-paeq-formula-witness pa194-paeq-bshift-growth pa194-paeq-term-subst-growth pa194-paeq-subst-growth pa194-paeq-subst-witness; do
  sha256sum -c "$base/$dir/upstream.sha256"
done
export PA194_PAEQ_SUBST_WITNESS_REPO="$PWD"
python3 - "$base/pa196-vs-u208/ipra/check.sh" "$root/paeq-subst-witness-prerequisites.sh" <<'PY'
from pathlib import Path
import sys
s = Path(sys.argv[1]).read_text()
old = 'repo=$(git -C "$(dirname "$0")" rev-parse --show-toplevel)'
marker = 'lean -M6000 -j1 "$bridge/PA196PASubstitutionWitnessComplete.lean" -o "$PA196_TASK_CHECK_DIR/PA196PASubstitutionWitnessComplete.olean" | tee -a "$PA196_TASK_CHECK_DIR/axioms.log"\n'
if s.count(old) != 1 or s.count(marker) != 1:
    raise SystemExit('unexpected substitution witness prerequisite wrapper')
s = s.replace(old, 'repo=$PA194_PAEQ_SUBST_WITNESS_REPO', 1)
s = s[:s.index(marker) + len(marker)] + '''for item in \
  "pa194-paeq-term-blueprint PA194PAeqTermBlueprint" \
  "pa194-paeq-term-blueprint PA194PAeqTermCode" \
  "pa194-paeq-formula PA194PAeqSyntax" \
  "pa194-paeq-formula PA194PAeqLanguage" \
  "pa194-paeq-formula PA194PAeqAtoms" \
  "pa194-paeq-formula PA194PAeqAtomCode" \
  "pa194-paeq-formula PA194PAeqFormulaConstruction" \
  "pa194-paeq-formula PA194PAeqFormulaCode" \
  "pa194-paeq-term-rank PA194PAeqTermRank" \
  "pa194-paeq-term-witness PA194PAeqAlphabetBounds" \
  "pa194-paeq-term-witness PA194PAeqTermWitness" \
  "pa194-paeq-term-witness PA194PAeqTermRecWitness" \
  "pa194-paeq-term-witness PA194PAeqTermOperations" \
  "pa194-paeq-formula-witness PA194PAeqFormulaWitness" \
  "pa194-paeq-subst-witness PA194PAeqFormulaRecWitness" \
  "pa194-paeq-subst-witness PA194PAeqQVecWitness" \
  "pa194-paeq-bshift-growth PA194PAeqBShiftGrowth" \
  "pa194-paeq-bshift-growth PA194PAeqQVecGrowth" \
  "pa194-paeq-term-subst-growth PA194PAeqTermSubstGrowth" \
  "pa194-paeq-term-subst-growth PA194PAeqTermSubstVecGrowth" \
  "pa194-paeq-subst-growth PA194PAeqSubstAtomicGrowth" \
  "pa194-paeq-subst-growth PA194PAeqSubstGraphStep" \
  "pa194-paeq-subst-growth PA194PAeqSubstUniformGrowth" \
  "pa194-paeq-subst-witness PA194PAeqSubstClauses" \
  "pa194-paeq-subst-witness PA194PAeqSubstNegative" \
  "pa194-paeq-subst-witness PA194PAeqSubstRel" \
  "pa194-paeq-subst-witness PA194PAeqSubstCore" \
  "pa194-paeq-subst-witness PA194PAeqSubstStageBounds" \
  "pa194-paeq-subst-witness PA194PAeqSubstStageUniform" \
  "pa194-paeq-subst-witness PA194PAeqSubstWitnessConditional" \
  "pa194-paeq-subst-witness PA194PAeqSubstWitnessComplete"; do
  read -r dir mod <<< "$item"
  lean -M6000 -j1 "Computability/BusyBeaver/Research/PA/$dir/$mod.lean" -o "$PA196_TASK_CHECK_DIR/$mod.olean" | tee -a "$PA196_TASK_CHECK_DIR/axioms.log"
done
if rg -q "sorryAx" "$PA196_TASK_CHECK_DIR/axioms.log"; then exit 1; fi
'\n'''
Path(sys.argv[2]).write_text(s)
PY
bash -n "$root/paeq-subst-witness-prerequisites.sh"
bash "$root/paeq-subst-witness-prerequisites.sh"
