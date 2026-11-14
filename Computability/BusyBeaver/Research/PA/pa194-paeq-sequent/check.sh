#!/usr/bin/env bash
set -euo pipefail
: "${IPRA_FOUNDATION_OVERLAY:?Set IPRA_FOUNDATION_OVERLAY to the audited Foundation object directory}"
: "${IPRA_LEAN_OVERLAY:?Set IPRA_LEAN_OVERLAY to the audited project object directory}"
base=Computability/BusyBeaver/Research/PA
root=$(mktemp -d "${TMPDIR:-/dev/shm}/pa194-paeq-sequent.XXXXXXXX")
trap 'rm -rf "$root"' EXIT
sha256sum -c "$base/pa194-paeq-term-blueprint/upstream.sha256"
sha256sum -c "$base/pa194-paeq-formula/upstream.sha256"
sha256sum -c "$base/pa194-paeq-translation-validity/upstream.sha256"
sha256sum -c "$base/pa194-paeq-translation-shift/upstream.sha256"
sha256sum -c "$base/pa194-paeq-formula-subst/upstream.sha256"
sha256sum -c "$base/pa194-paeq-formula-shift/upstream.sha256"
sha256sum -c "$base/pa194-paeq-sequent/upstream.sha256"
export LEAN_PATH="$root:$IPRA_LEAN_OVERLAY:$IPRA_FOUNDATION_OVERLAY:$(lake env printenv LEAN_PATH)"
for mod in PA194PAeqTermBlueprint PA194PAeqTermCode; do
  lean -M6000 -j1 -o "$root/$mod.olean" "$base/pa194-paeq-term-blueprint/$mod.lean" | tee -a "$root/axioms.log"
done
for mod in PA194PAeqSyntax PA194PAeqLanguage PA194PAeqAtoms PA194PAeqAtomCode PA194PAeqFormulaConstruction PA194PAeqFormulaCode; do
  lean -M6000 -j1 -o "$root/$mod.olean" "$base/pa194-paeq-formula/$mod.lean" | tee -a "$root/axioms.log"
done
for mod in PA194PAeqTermValidity PA194PAeqAtomValidity PA194PAeqFormulaValidity; do
  lean -M6000 -j1 -o "$root/$mod.olean" "$base/pa194-paeq-translation-validity/$mod.lean" | tee -a "$root/axioms.log"
done
for mod in PA194PAeqTranslationShift PA194PAeqTranslationBShift PA194PAeqTranslationQVec PA194PAeqTranslationTermSubst; do
  lean -M6000 -j1 -o "$root/$mod.olean" "$base/pa194-paeq-translation-shift/$mod.lean" | tee -a "$root/axioms.log"
done
for mod in PA194PAeqAtomCompatibility PA194PAeqAtomTransport PA194PAeqFormulaSubst; do
  lean -M6000 -j1 -o "$root/$mod.olean" "$base/pa194-paeq-formula-subst/$mod.lean" | tee -a "$root/axioms.log"
done
for mod in PA194PAeqFormulaShift PA194PAeqFormulaClosure; do
  lean -M6000 -j1 -o "$root/$mod.olean" "$base/pa194-paeq-formula-shift/$mod.lean" | tee -a "$root/axioms.log"
done
lean -M6000 -j1 -o "$root/PA194PAeqNegation.olean" "$base/pa194-paeq-sequent/PA194PAeqNegation.lean" | tee -a "$root/axioms.log"
lean -M6000 -j1 -o "$root/PA194PAeqSequent.olean" "$base/pa194-paeq-sequent/PA194PAeqSequent.lean" | tee -a "$root/axioms.log"
if rg -q 'sorryAx' "$root/axioms.log"; then exit 1; fi
