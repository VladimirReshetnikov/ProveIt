#!/usr/bin/env bash
set -euo pipefail
: "${IPRA_FOUNDATION_OVERLAY:?Set IPRA_FOUNDATION_OVERLAY to the audited Foundation object directory}"
: "${IPRA_LEAN_OVERLAY:?Set IPRA_LEAN_OVERLAY to the audited project object directory}"
base=Computability/BusyBeaver/Research/PA
root=$(mktemp -d "${TMPDIR:-/dev/shm}/pa194-paeq-term-translation-growth.XXXXXXXX")
trap 'rm -rf "$root"' EXIT
for dir in pa194-paeq-term-blueprint pa194-paeq-formula pa194-paeq-translation-validity; do
  sha256sum -c "$base/$dir/upstream.sha256"
done
export PA194_TERM_TRANSLATION_GROWTH_REPO="$PWD"
python3 - "$base/pa196-vs-u208/ipra/check.sh" "$root/term-translation-growth-prerequisites.sh" <<'PY'
from pathlib import Path
import sys
s = Path(sys.argv[1]).read_text()
old = 'repo=$(git -C "$(dirname "$0")" rev-parse --show-toplevel)'
marker = 'lean -M6000 -j1 "$bridge/PA196PATermBShiftGrowth.lean" -o "$PA196_TASK_CHECK_DIR/PA196PATermBShiftGrowth.olean" | tee -a "$PA196_TASK_CHECK_DIR/axioms.log"\n'
if s.count(old) != 1 or s.count(marker) != 1:
    raise SystemExit('unexpected term-growth prerequisite wrapper')
s = s.replace(old, 'repo=$PA194_TERM_TRANSLATION_GROWTH_REPO', 1)
s = s[:s.index(marker) + len(marker)] + '''for item in \
  "pa194-paeq-term-blueprint PA194PAeqTermBlueprint" \
  "pa194-paeq-term-blueprint PA194PAeqTermCode" \
  "pa194-paeq-formula PA194PAeqSyntax" \
  "pa194-paeq-formula PA194PAeqLanguage" \
  "pa194-paeq-formula PA194PAeqAtoms" \
  "pa194-paeq-formula PA194PAeqAtomCode" \
  "pa194-paeq-formula PA194PAeqFormulaConstruction" \
  "pa194-paeq-formula PA194PAeqFormulaCode" \
  "pa194-paeq-translation-validity PA194PAeqTermValidity" \
  "pa194-paeq-translation-validity PA194PAeqAtomValidity" \
  "pa194-paeq-translation-validity PA194PAeqFormulaValidity" \
  "pa194-paeq-term-translation-growth PA194PAeqTermTranslationGrowth"; do
  read -r dir mod <<< "$item"
  lean -M6000 -j1 "Computability/BusyBeaver/Research/PA/$dir/$mod.lean" -o "$PA196_TASK_CHECK_DIR/$mod.olean" | tee -a "$PA196_TASK_CHECK_DIR/axioms.log"
done
if rg -q "sorryAx" "$PA196_TASK_CHECK_DIR/axioms.log"; then exit 1; fi
'\n'''
Path(sys.argv[2]).write_text(s)
PY
bash -n "$root/term-translation-growth-prerequisites.sh"
bash "$root/term-translation-growth-prerequisites.sh"
