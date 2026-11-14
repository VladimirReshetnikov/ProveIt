#!/usr/bin/env bash
set -euo pipefail

# The two dependency overlays must have been built from the matching sources;
# see README.md.  This script rebuilds the literal-machine and bridge modules.
: "${IPRA_LEAN_OVERLAY:?Set IPRA_LEAN_OVERLAY to the built iPRA module directory}"
: "${IPRA_FOUNDATION_OVERLAY:?Set IPRA_FOUNDATION_OVERLAY to the built Foundation module directory}"
repo=$(git -C "$(dirname "$0")" rev-parse --show-toplevel)
cd "$repo"
IPRA_LEAN_OVERLAY=$(realpath "$IPRA_LEAN_OVERLAY")
IPRA_FOUNDATION_OVERLAY=$(realpath "$IPRA_FOUNDATION_OVERLAY")
test -d "$IPRA_LEAN_OVERLAY/DiophantineConsistency"

sha256sum -c <<'PINS'
152d1d552b27baca8db0ac05b16092d9083c2ab979bb0b4e7f96a95803d9a9b0  Computability/BusyBeaver/Research/PA/jamesyc-upstream/pa196/M6/Zip.lean
e5ed123ad8e54d431472621d46b6f147a76ed94426efc9e9298f475e8ecca944  Computability/BusyBeaver/Research/PA/jamesyc-upstream/pa196/PA196/Literal.lean
e8bbccd4cfa325251ca95066db116b5aa766e404b0971c33c02772be1c3617a8  Computability/BusyBeaver/Research/PA/jamesyc-upstream/pa196/data/pa196.tm
5e21edfdc4593f441f46f7fde9f8d0fc467eb1369c03251fe4f3a1a4d17a57de  Computability/DiophantineConsistency/Lean/DiophantineConsistency/PRALanguage.lean
f0a5ba7482344477c2c7ca5ec2544f127ede62ec30e60b1101bfaed7be94db74  Computability/DiophantineConsistency/Lean/DiophantineConsistency/PRAFiniteFunctionCodes.lean
PINS

task_dir=$(mktemp -d "${TMPDIR:-/tmp}/pa196-ipra-check.XXXXXXXX")
trap 'rm -rf "$task_dir"' EXIT
mkdir -p "$task_dir/M6" "$task_dir/PA196" "$task_dir/DiophantineConsistency"
# A module namespace is resolved from one search-path root.  Link the
# existing dependency objects into our private overlay so that rebuilding the
# PA-consistency module below does not hide its other imports.
for task_dep in "$IPRA_LEAN_OVERLAY"/DiophantineConsistency/*; do
  task_name=${task_dep##*/}
  case "$task_name" in IPRAPA196Consistency.olean*|PRAWitnessRefutationOuter.olean*) continue ;; esac
  ln -s "$task_dep" "$task_dir/DiophantineConsistency/$task_name"
done
export PA196_TASK_CHECK_DIR="$task_dir" IPRA_LEAN_OVERLAY IPRA_FOUNDATION_OVERLAY
lake env bash -c '
set -euo pipefail
lean --version | rg -q "Lean \(version 4\.32\.0"
export LEAN_PATH="$PA196_TASK_CHECK_DIR:$IPRA_LEAN_OVERLAY:$IPRA_FOUNDATION_OVERLAY:${LEAN_PATH:-}"
upstream=Computability/BusyBeaver/Research/PA/jamesyc-upstream/pa196
bridge=Computability/BusyBeaver/Research/PA/pa196-vs-u208/ipra
lean -M6000 -j1 "$upstream/M6/Zip.lean" -o "$PA196_TASK_CHECK_DIR/M6/Zip.olean"
lean -M6000 -j1 "$upstream/PA196/Literal.lean" -o "$PA196_TASK_CHECK_DIR/PA196/Literal.olean"
lean -M6000 -j1 "$bridge/PA196Bounded.lean" -o "$PA196_TASK_CHECK_DIR/PA196Bounded.olean"
lean -M6000 -j1 Computability/DiophantineConsistency/Lean/DiophantineConsistency/IPRAPA196Consistency.lean \
  -o "$PA196_TASK_CHECK_DIR/DiophantineConsistency/IPRAPA196Consistency.olean"
lean -M6000 -j1 Computability/DiophantineConsistency/Lean/DiophantineConsistency/PRAWitnessRefutationOuter.lean \
  -o "$PA196_TASK_CHECK_DIR/DiophantineConsistency/PRAWitnessRefutationOuter.olean"
lean -M6000 -j1 "$bridge/PA196BoundedChecks.lean" | tee "$PA196_TASK_CHECK_DIR/axioms.log"
lean -M6000 -j1 "$bridge/PA196Endpoint.lean" -o "$PA196_TASK_CHECK_DIR/PA196Endpoint.olean" | tee -a "$PA196_TASK_CHECK_DIR/axioms.log"
lean -M6000 -j1 "$bridge/PA196StandardSemantics.lean" | tee -a "$PA196_TASK_CHECK_DIR/axioms.log"
lean -M6000 -j1 "$bridge/PA196ForwardGG.lean" -o "$PA196_TASK_CHECK_DIR/PA196ForwardGG.olean" | tee -a "$PA196_TASK_CHECK_DIR/axioms.log"
lean -M6000 -j1 "$bridge/PA196ReverseGG.lean" -o "$PA196_TASK_CHECK_DIR/PA196ReverseGG.olean" | tee -a "$PA196_TASK_CHECK_DIR/axioms.log"
lean -M6000 -j1 "$bridge/PA196PRAAssembly.lean" | tee -a "$PA196_TASK_CHECK_DIR/axioms.log"
lean -M6000 -j1 "$bridge/PA196PACoreBound.lean" | tee -a "$PA196_TASK_CHECK_DIR/axioms.log"
lean -M6000 -j1 "$bridge/PA196PAMinusWitness.lean" -o "$PA196_TASK_CHECK_DIR/PA196PAMinusWitness.olean" | tee -a "$PA196_TASK_CHECK_DIR/axioms.log"
lean -M6000 -j1 "$bridge/PA196PAAxiomBound.lean" -o "$PA196_TASK_CHECK_DIR/PA196PAAxiomBound.olean" | tee -a "$PA196_TASK_CHECK_DIR/axioms.log"
lean -M6000 -j1 "$bridge/PA196PASimpleRuleBounds.lean" | tee -a "$PA196_TASK_CHECK_DIR/axioms.log"
lean -M6000 -j1 "$bridge/PA196PAAxiomAssembly.lean" | tee -a "$PA196_TASK_CHECK_DIR/axioms.log"
lean -M6000 -j1 "$bridge/PA196InductionClosureWitness.lean" | tee -a "$PA196_TASK_CHECK_DIR/axioms.log"
lean -M6000 -j1 "$bridge/PA196InductionFvarWitness.lean" | tee -a "$PA196_TASK_CHECK_DIR/axioms.log"
lean -M6000 -j1 "$bridge/PA196InductionBodyAll.lean" -o "$PA196_TASK_CHECK_DIR/PA196InductionBodyAll.olean" | tee -a "$PA196_TASK_CHECK_DIR/axioms.log"
lean -M6000 -j1 "$bridge/PA196PAAlphabetBounds.lean" -o "$PA196_TASK_CHECK_DIR/PA196PAAlphabetBounds.olean" | tee -a "$PA196_TASK_CHECK_DIR/axioms.log"
lean -M6000 -j1 "$bridge/PA196PAFormulaBound.lean" -o "$PA196_TASK_CHECK_DIR/PA196PAFormulaBound.olean" | tee -a "$PA196_TASK_CHECK_DIR/axioms.log"
lean -M6000 -j1 "$bridge/PA196PATermBounds.lean" -o "$PA196_TASK_CHECK_DIR/PA196PATermBounds.olean" | tee -a "$PA196_TASK_CHECK_DIR/axioms.log"
lean -M6000 -j1 "$bridge/PA196PAFormulaComplete.lean" -o "$PA196_TASK_CHECK_DIR/PA196PAFormulaComplete.olean" | tee -a "$PA196_TASK_CHECK_DIR/axioms.log"
lean -M6000 -j1 "$bridge/PA196PAFormulaRecBound.lean" -o "$PA196_TASK_CHECK_DIR/PA196PAFormulaRecBound.olean" | tee -a "$PA196_TASK_CHECK_DIR/axioms.log"
lean -M6000 -j1 "$bridge/PA196PANegationBound.lean" -o "$PA196_TASK_CHECK_DIR/PA196PANegationBound.olean" | tee -a "$PA196_TASK_CHECK_DIR/axioms.log"
lean -M6000 -j1 "$bridge/PA196InductionImpGrowth.lean" -o "$PA196_TASK_CHECK_DIR/PA196InductionImpGrowth.olean" | tee -a "$PA196_TASK_CHECK_DIR/axioms.log"
lean -M6000 -j1 "$bridge/PA196InductionBodyTail.lean" -o "$PA196_TASK_CHECK_DIR/PA196InductionBodyTail.olean" | tee -a "$PA196_TASK_CHECK_DIR/axioms.log"
lean -M6000 -j1 "$bridge/PA196InductionBodyImp.lean" -o "$PA196_TASK_CHECK_DIR/PA196InductionBodyImp.olean" | tee -a "$PA196_TASK_CHECK_DIR/axioms.log"
lean -M6000 -j1 "$bridge/PA196InductionBodyOuter.lean" | tee -a "$PA196_TASK_CHECK_DIR/axioms.log"
lean -M6000 -j1 "$bridge/PA196PANegBoundTerms.lean" -o "$PA196_TASK_CHECK_DIR/PA196PANegBoundTerms.olean" | tee -a "$PA196_TASK_CHECK_DIR/axioms.log"
lean -M6000 -j1 "$bridge/PA196PAIdentityBounds.lean" | tee -a "$PA196_TASK_CHECK_DIR/axioms.log"
lean -M6000 -j1 "$bridge/PA196PACutBounds.lean" | tee -a "$PA196_TASK_CHECK_DIR/axioms.log"
lean -M6000 -j1 "$bridge/PA196PABvGrowth.lean" -o "$PA196_TASK_CHECK_DIR/PA196PABvGrowth.olean" | tee -a "$PA196_TASK_CHECK_DIR/axioms.log"
lean -M6000 -j1 "$bridge/PA196PATermRankGeneral.lean" -o "$PA196_TASK_CHECK_DIR/PA196PATermRankGeneral.olean" | tee -a "$PA196_TASK_CHECK_DIR/axioms.log"
lean -M6000 -j1 "$bridge/PA196PATermBVRank.lean" -o "$PA196_TASK_CHECK_DIR/PA196PATermBVRank.olean" | tee -a "$PA196_TASK_CHECK_DIR/axioms.log"
lean -M6000 -j1 "$bridge/PA196PATermRecBound.lean" -o "$PA196_TASK_CHECK_DIR/PA196PATermRecBound.olean" | tee -a "$PA196_TASK_CHECK_DIR/axioms.log"
lean -M6000 -j1 "$bridge/PA196PATermOperations.lean" -o "$PA196_TASK_CHECK_DIR/PA196PATermOperations.olean" | tee -a "$PA196_TASK_CHECK_DIR/axioms.log"
lean -M6000 -j1 "$bridge/PA196PAQVecGraph.lean" -o "$PA196_TASK_CHECK_DIR/PA196PAQVecGraph.olean" | tee -a "$PA196_TASK_CHECK_DIR/axioms.log"
lean -M6000 -j1 "$bridge/PA196PAQVecLength.lean" | tee -a "$PA196_TASK_CHECK_DIR/axioms.log"
lean -M6000 -j1 "$bridge/PA196PATermBShiftGrowth.lean" -o "$PA196_TASK_CHECK_DIR/PA196PATermBShiftGrowth.olean" | tee -a "$PA196_TASK_CHECK_DIR/axioms.log"
lean -M6000 -j1 "$bridge/PA196PAQVecGrowth.lean" -o "$PA196_TASK_CHECK_DIR/PA196PAQVecGrowth.olean" | tee -a "$PA196_TASK_CHECK_DIR/axioms.log"
lean -M6000 -j1 "$bridge/PA196PRAQVecTower.lean" -o "$PA196_TASK_CHECK_DIR/PA196PRAQVecTower.olean" | tee -a "$PA196_TASK_CHECK_DIR/axioms.log"
lean -M6000 -j1 "$bridge/PA196PAQVecTowerModel.lean" | tee -a "$PA196_TASK_CHECK_DIR/axioms.log"
lean -M6000 -j1 "$bridge/PA196PAQVecTraceInvariant.lean" | tee -a "$PA196_TASK_CHECK_DIR/axioms.log"
lean -M6000 -j1 "$bridge/PA196PAQVecSeqTrace.lean" | tee -a "$PA196_TASK_CHECK_DIR/axioms.log"
lean -M6000 -j1 "$bridge/PA196PASubstitutionClauses.lean" -o "$PA196_TASK_CHECK_DIR/PA196PASubstitutionClauses.olean" | tee -a "$PA196_TASK_CHECK_DIR/axioms.log"
lean -M6000 -j1 "$bridge/PA196PASubstitutionNegative.lean" -o "$PA196_TASK_CHECK_DIR/PA196PASubstitutionNegative.olean" | tee -a "$PA196_TASK_CHECK_DIR/axioms.log"
lean -M6000 -j1 "$bridge/PA196PASubstitutionCore.lean" -o "$PA196_TASK_CHECK_DIR/PA196PASubstitutionCore.olean" | tee -a "$PA196_TASK_CHECK_DIR/axioms.log"
lean -M6000 -j1 "$bridge/PA196PATermSubstGrowth.lean" -o "$PA196_TASK_CHECK_DIR/PA196PATermSubstGrowth.olean" | tee -a "$PA196_TASK_CHECK_DIR/axioms.log"
lean -M6000 -j1 "$bridge/PA196PATermSubstVecGrowth.lean" -o "$PA196_TASK_CHECK_DIR/PA196PATermSubstVecGrowth.olean" | tee -a "$PA196_TASK_CHECK_DIR/axioms.log"
lean -M6000 -j1 "$bridge/PA196PASubstitutionRel.lean" -o "$PA196_TASK_CHECK_DIR/PA196PASubstitutionRel.olean" | tee -a "$PA196_TASK_CHECK_DIR/axioms.log"
lean -M6000 -j1 "$bridge/PA196PASubstitutionCoreComplete.lean" | tee -a "$PA196_TASK_CHECK_DIR/axioms.log"
lean -M6000 -j1 "$bridge/PA196PATermBVGraph.lean" -o "$PA196_TASK_CHECK_DIR/PA196PATermBVGraph.olean" | tee -a "$PA196_TASK_CHECK_DIR/axioms.log"
lean -M6000 -j1 "$bridge/PA196PABvGraphBound.lean" -o "$PA196_TASK_CHECK_DIR/PA196PABvGraphBound.olean" | tee -a "$PA196_TASK_CHECK_DIR/axioms.log"
lean -M6000 -j1 "$bridge/PA196PAFormulaSetBound.lean" -o "$PA196_TASK_CHECK_DIR/PA196PAFormulaSetBound.olean" | tee -a "$PA196_TASK_CHECK_DIR/axioms.log"
lean -M6000 -j1 "$bridge/PA196PAFormulaSetComplete.lean" | tee -a "$PA196_TASK_CHECK_DIR/axioms.log"
if rg -q "sorryAx" "$PA196_TASK_CHECK_DIR/axioms.log"; then
  echo "Unexpected sorryAx in theorem dependencies" >&2
  exit 1
fi
'
