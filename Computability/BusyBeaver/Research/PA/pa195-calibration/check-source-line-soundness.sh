#!/usr/bin/env bash
set -euo pipefail
: "${IPRA_LEAN_OVERLAY:?Set IPRA_LEAN_OVERLAY to the matching audited project object directory}"
: "${IPRA_FOUNDATION_OVERLAY:?Set IPRA_FOUNDATION_OVERLAY to the matching audited Foundation object directory}"
repo=$(git -C "$(dirname "$0")" rev-parse --show-toplevel)
cd "$repo"
IPRA_LEAN_OVERLAY=$(realpath "$IPRA_LEAN_OVERLAY")
IPRA_FOUNDATION_OVERLAY=$(realpath "$IPRA_FOUNDATION_OVERLAY")
sha256sum --strict -c <<'PINS'
aadfdeb41e75c1652b555ed996fea5d15d7f1b9f65c7c553823a99773ee24c84  Computability/BusyBeaver/Lean/BusyBeaver/ZFC/ArithmeticCantor.lean
d7ea33865ce8c7ce192a0abf1bbd7246dee3a00d595491027ac75b711831ac40  Computability/DiophantineConsistency/Lean/DiophantineConsistency/PRAWitnessTransfer.lean
PINS
printf '%s  %s\n' \
  73992c2c19e098f4e60767aaab2c5dedf37f6a90a81adb561034848fd20f5ab7 "$IPRA_LEAN_OVERLAY/BusyBeaver/ZFC/ArithmeticCantor.olean" \
  c8e29b70f19c4dc4f85fdaf8b3e053f7628a939915cac1be270b4774e6133e0b "$IPRA_LEAN_OVERLAY/DiophantineConsistency/PRAWitnessTransfer.olean" | sha256sum --strict -c
task_dir=$(mktemp -d "${TMPDIR:-/dev/shm}/pa194-source-line-soundness.XXXXXXXX")
trap 'rm -rf "$task_dir"' EXIT
cp -as "$IPRA_LEAN_OVERLAY/." "$task_dir/"
export LEAN_PATH="$task_dir:$IPRA_FOUNDATION_OVERLAY:$(lake env printenv LEAN_PATH)"
for name in PRAHistoryLengthUnique PRAHistorySingletonMembership PRAHistorySingletonSequence PRAHistoryIterator PRAHistoryTrace PRAHistoryResultGraph; do
  rm -f "$task_dir/DiophantineConsistency/$name.olean"
  lean -M6000 -j1 -o "$task_dir/DiophantineConsistency/$name.olean" "Computability/DiophantineConsistency/Lean/DiophantineConsistency/$name.lean"
done
for name in PA194ParamRecursionGraph PA194ParamIterator PA194ParamTrace; do
  lean -M6000 -j1 -o "$task_dir/$name.olean" "Computability/BusyBeaver/Research/PA/pa195-calibration/$name.lean" | tee -a "$task_dir/axioms.log"
done
for name in PA194ParamRecursionDefined PA194ParamComp; do
  lean -M6000 -j1 -o "$task_dir/$name.olean" "Computability/BusyBeaver/Research/PA/pa195-calibration/$name.lean" | tee -a "$task_dir/axioms.log"
done
lean -M6000 -j1 -o "$task_dir/PA194CodeGraph.olean" Computability/BusyBeaver/Research/PA/pa195-calibration/PA194CodeGraph.lean | tee -a "$task_dir/axioms.log"
lean -M6000 -j1 -o "$task_dir/PA194CodeInstance.olean" Computability/BusyBeaver/Research/PA/pa195-calibration/PA194CodeInstance.lean | tee -a "$task_dir/axioms.log"
lean -M6000 -j1 -o "$task_dir/PA195FreshBound.olean" Computability/BusyBeaver/Research/PA/pa195-calibration/PA195FreshBound.lean
lean -M6000 -j1 -o "$task_dir/PA195DecodedFields.olean" Computability/BusyBeaver/Research/PA/pa195-calibration/PA195DecodedFields.lean
lean -M6000 -j1 -o "$task_dir/PA194ChildCodes.olean" Computability/BusyBeaver/Research/PA/pa195-calibration/PA194ChildCodes.lean
lean -M6000 -j1 -o "$task_dir/PA195PathBound.olean" Computability/BusyBeaver/Research/PA/pa195-calibration/PA195PathBound.lean
lean -M6000 -j1 -o "$task_dir/PA194PathZero.olean" Computability/BusyBeaver/Research/PA/pa195-calibration/PA194PathZero.lean
lean -M6000 -j1 -o "$task_dir/PA194PathIterator.olean" Computability/BusyBeaver/Research/PA/pa195-calibration/PA194PathIterator.lean
lean -M6000 -j1 -o "$task_dir/PA194BranchSeed.olean" Computability/BusyBeaver/Research/PA/pa195-calibration/PA194BranchSeed.lean
lean -M6000 -j1 -o "$task_dir/PA194FVarCode.olean" Computability/BusyBeaver/Research/PA/pa195-calibration/PA194FVarCode.lean | tee -a "$task_dir/axioms.log"
lean -M6000 -j1 -o "$task_dir/PA194BVarCode.olean" Computability/BusyBeaver/Research/PA/pa195-calibration/PA194BVarCode.lean | tee -a "$task_dir/axioms.log"
lean -M6000 -j1 -o "$task_dir/PA194CloseVariable.olean" Computability/BusyBeaver/Research/PA/pa195-calibration/PA194CloseVariable.lean | tee -a "$task_dir/axioms.log"
lean -M6000 -j1 -o "$task_dir/PA194StackCode.olean" Computability/BusyBeaver/Research/PA/pa195-calibration/PA194StackCode.lean | tee -a "$task_dir/axioms.log"
lean -M6000 -j1 -o "$task_dir/PA194VariableDispatch.olean" Computability/BusyBeaver/Research/PA/pa195-calibration/PA194VariableDispatch.lean | tee -a "$task_dir/axioms.log"
lean -M6000 -j1 -o "$task_dir/PA194NumeralCode.olean" Computability/BusyBeaver/Research/PA/pa195-calibration/PA194NumeralCode.lean | tee -a "$task_dir/axioms.log"
lean -M6000 -j1 -o "$task_dir/PA194QuadCode.olean" Computability/BusyBeaver/Research/PA/pa195-calibration/PA194QuadCode.lean | tee -a "$task_dir/axioms.log"
lean -M6000 -j1 -o "$task_dir/PA194TagCode.olean" Computability/BusyBeaver/Research/PA/pa195-calibration/PA194TagCode.lean | tee -a "$task_dir/axioms.log"
lean -M6000 -j1 -o "$task_dir/PA194CloseFunction.olean" Computability/BusyBeaver/Research/PA/pa195-calibration/PA194CloseFunction.lean | tee -a "$task_dir/axioms.log"
lean -M6000 -j1 -o "$task_dir/PA194TermDispatch.olean" Computability/BusyBeaver/Research/PA/pa195-calibration/PA194TermDispatch.lean | tee -a "$task_dir/axioms.log"
lean -M6000 -j1 -o "$task_dir/PA194CloseBounded.olean" Computability/BusyBeaver/Research/PA/pa195-calibration/PA194CloseBounded.lean | tee -a "$task_dir/axioms.log"
lean -M6000 -j1 -o "$task_dir/PA194StackHistory.olean" Computability/BusyBeaver/Research/PA/pa195-calibration/PA194StackHistory.lean | tee -a "$task_dir/axioms.log"
lean -M6000 -j1 -o "$task_dir/PA194ParamHistory.olean" Computability/BusyBeaver/Research/PA/pa195-calibration/PA194ParamHistory.lean | tee -a "$task_dir/axioms.log"
lean -M6000 -j1 -o "$task_dir/PA194TermHistory.olean" Computability/BusyBeaver/Research/PA/pa195-calibration/PA194TermHistory.lean | tee -a "$task_dir/axioms.log"
lean -M6000 -j1 -o "$task_dir/PA194TermRecursion.olean" Computability/BusyBeaver/Research/PA/pa195-calibration/PA194TermRecursion.lean | tee -a "$task_dir/axioms.log"
lean -M6000 -j1 -o "$task_dir/PA194TermWellFormed.olean" Computability/BusyBeaver/Research/PA/pa195-calibration/PA194TermWellFormed.lean | tee -a "$task_dir/axioms.log"
lean -M6000 -j1 -o "$task_dir/PA194TermWellFormedUnconditional.olean" Computability/BusyBeaver/Research/PA/pa195-calibration/PA194TermWellFormedUnconditional.lean | tee -a "$task_dir/axioms.log"
lean -M6000 -j1 -o "$task_dir/PA194InternalClose.olean" Computability/BusyBeaver/Research/PA/pa195-calibration/PA194InternalClose.lean | tee -a "$task_dir/axioms.log"
lean -M6000 -j1 -o "$task_dir/PA194InternalFormulaClose.olean" Computability/BusyBeaver/Research/PA/pa195-calibration/PA194InternalFormulaClose.lean | tee -a "$task_dir/axioms.log"
lean -M6000 -j1 -o "$task_dir/PA194ShiftFixedClose.olean" Computability/BusyBeaver/Research/PA/pa195-calibration/PA194ShiftFixedClose.lean | tee -a "$task_dir/axioms.log"
lean -M6000 -j1 -o "$task_dir/PA194InductionAxiomReopen.olean" Computability/BusyBeaver/Research/PA/pa195-calibration/PA194InductionAxiomReopen.lean | tee -a "$task_dir/axioms.log"
lean -M6000 -j1 -o "$task_dir/PA194PAAxiomReopen.olean" Computability/BusyBeaver/Research/PA/pa195-calibration/PA194PAAxiomReopen.lean | tee -a "$task_dir/axioms.log"
lean -M6000 -j1 -o "$task_dir/PA194LiftRename.olean" Computability/BusyBeaver/Research/PA/pa195-calibration/PA194LiftRename.lean | tee -a "$task_dir/axioms.log"
lean -M6000 -j1 -o "$task_dir/PA194GenericRenameBase.olean" Computability/BusyBeaver/Research/PA/pa195-calibration/PA194GenericRenameBase.lean | tee -a "$task_dir/axioms.log"
lean -M6000 -j1 -o "$task_dir/PA194GenericRenameAxiom.olean" Computability/BusyBeaver/Research/PA/pa195-calibration/PA194GenericRenameAxiom.lean | tee -a "$task_dir/axioms.log"
lean -M6000 -j1 -o "$task_dir/PA194ExpandedRename.olean" Computability/BusyBeaver/Research/PA/pa195-calibration/PA194ExpandedRename.lean | tee -a "$task_dir/axioms.log"
lean -M6000 -j1 -o "$task_dir/PA194GenericRenameRules.olean" Computability/BusyBeaver/Research/PA/pa195-calibration/PA194GenericRenameRules.lean | tee -a "$task_dir/axioms.log"
lean -M6000 -j1 -o "$task_dir/PA194RenameShiftCompatibility.olean" Computability/BusyBeaver/Research/PA/pa195-calibration/PA194RenameShiftCompatibility.lean | tee -a "$task_dir/axioms.log"
lean -M6000 -j1 -o "$task_dir/PA194RenameSubstitution.olean" Computability/BusyBeaver/Research/PA/pa195-calibration/PA194RenameSubstitution.lean | tee -a "$task_dir/axioms.log"
lean -M6000 -j1 -o "$task_dir/PA194RenameContexts.olean" Computability/BusyBeaver/Research/PA/pa195-calibration/PA194RenameContexts.lean | tee -a "$task_dir/axioms.log"
lean -M6000 -j1 -o "$task_dir/PA194RenameDerivationCases.olean" Computability/BusyBeaver/Research/PA/pa195-calibration/PA194RenameDerivationCases.lean | tee -a "$task_dir/axioms.log"
lean -M6000 -j1 -o "$task_dir/PA194RenameDerivation.olean" Computability/BusyBeaver/Research/PA/pa195-calibration/PA194RenameDerivation.lean | tee -a "$task_dir/axioms.log"
lean -M6000 -j1 -o "$task_dir/PA194FormulaBudget.olean" Computability/BusyBeaver/Research/PA/pa195-calibration/PA194FormulaBudget.lean | tee -a "$task_dir/axioms.log"
lean -M6000 -j1 -o "$task_dir/PA194FormulaUpdate.olean" Computability/BusyBeaver/Research/PA/pa195-calibration/PA194FormulaUpdate.lean | tee -a "$task_dir/axioms.log"
lean -M6000 -j1 -o "$task_dir/PA194FormulaAgreement.olean" Computability/BusyBeaver/Research/PA/pa195-calibration/PA194FormulaAgreement.lean | tee -a "$task_dir/axioms.log"
lean -M6000 -j1 -o "$task_dir/PA194TagDecoder.olean" Computability/BusyBeaver/Research/PA/pa195-calibration/PA194TagDecoder.lean | tee -a "$task_dir/axioms.log"
lean -M6000 -j1 -o "$task_dir/PA194DispatchCode.olean" Computability/BusyBeaver/Research/PA/pa195-calibration/PA194DispatchCode.lean | tee -a "$task_dir/axioms.log"
lean -M6000 -j1 -o "$task_dir/PA194HistoryDispatch.olean" Computability/BusyBeaver/Research/PA/pa195-calibration/PA194HistoryDispatch.lean | tee -a "$task_dir/axioms.log"
lean -M6000 -j1 -o "$task_dir/PA194BitTemplate.olean" Computability/BusyBeaver/Research/PA/pa195-calibration/PA194BitTemplate.lean | tee -a "$task_dir/axioms.log"
lean -M6000 -j1 -o "$task_dir/PA194TemplateInternal.olean" Computability/BusyBeaver/Research/PA/pa195-calibration/PA194TemplateInternal.lean | tee -a "$task_dir/axioms.log"
lean -M6000 -j1 -o "$task_dir/PA194MembershipCode.olean" Computability/BusyBeaver/Research/PA/pa195-calibration/PA194MembershipCode.lean | tee -a "$task_dir/axioms.log"
lean -M6000 -j1 -o "$task_dir/PA194CanonicalVectorCode.olean" Computability/BusyBeaver/Research/PA/pa195-calibration/PA194CanonicalVectorCode.lean | tee -a "$task_dir/axioms.log"
lean -M6000 -j1 -o "$task_dir/PA194RelCode.olean" Computability/BusyBeaver/Research/PA/pa195-calibration/PA194RelCode.lean | tee -a "$task_dir/axioms.log"
lean -M6000 -j1 -o "$task_dir/PA194CanonicalAtomCode.olean" Computability/BusyBeaver/Research/PA/pa195-calibration/PA194CanonicalAtomCode.lean | tee -a "$task_dir/axioms.log"
lean -M6000 -j1 -o "$task_dir/PA194EqAtomCode.olean" Computability/BusyBeaver/Research/PA/pa195-calibration/PA194EqAtomCode.lean | tee -a "$task_dir/axioms.log"
lean -M6000 -j1 -o "$task_dir/PA194EqualityCode.olean" Computability/BusyBeaver/Research/PA/pa195-calibration/PA194EqualityCode.lean | tee -a "$task_dir/axioms.log"
lean -M6000 -j1 -o "$task_dir/PA194DualAtomCode.olean" Computability/BusyBeaver/Research/PA/pa195-calibration/PA194DualAtomCode.lean | tee -a "$task_dir/axioms.log"
lean -M6000 -j1 -o "$task_dir/PA194DualImpCode.olean" Computability/BusyBeaver/Research/PA/pa195-calibration/PA194DualImpCode.lean | tee -a "$task_dir/axioms.log"
lean -M6000 -j1 -o "$task_dir/PA194DualRecursion.olean" Computability/BusyBeaver/Research/PA/pa195-calibration/PA194DualRecursion.lean | tee -a "$task_dir/axioms.log"
lean -M6000 -j1 -o "$task_dir/PA194DualForallCode.olean" Computability/BusyBeaver/Research/PA/pa195-calibration/PA194DualForallCode.lean | tee -a "$task_dir/axioms.log"
lean -M6000 -j1 -o "$task_dir/PA194DualQuantRecursion.olean" Computability/BusyBeaver/Research/PA/pa195-calibration/PA194DualQuantRecursion.lean | tee -a "$task_dir/axioms.log"
lean -M6000 -j1 -o "$task_dir/PA194CanonicalDualForall.olean" Computability/BusyBeaver/Research/PA/pa195-calibration/PA194CanonicalDualForall.lean | tee -a "$task_dir/axioms.log"
lean -M6000 -j1 -o "$task_dir/PA194SourceOutputWF.olean" Computability/BusyBeaver/Research/PA/pa195-calibration/PA194SourceOutputWF.lean | tee -a "$task_dir/axioms.log"
lean -M6000 -j1 -o "$task_dir/PA194CloseNegation.olean" Computability/BusyBeaver/Research/PA/pa195-calibration/PA194CloseNegation.lean | tee -a "$task_dir/axioms.log"
lean -M6000 -j1 -o "$task_dir/PA194DualComplement.olean" Computability/BusyBeaver/Research/PA/pa195-calibration/PA194DualComplement.lean | tee -a "$task_dir/axioms.log"
lean -M6000 -j1 -o "$task_dir/PA194SourcePolarity.olean" Computability/BusyBeaver/Research/PA/pa195-calibration/PA194SourcePolarity.lean | tee -a "$task_dir/axioms.log"
lean -M6000 -j1 -o "$task_dir/PA194SourceAllPreservation.olean" Computability/BusyBeaver/Research/PA/pa195-calibration/PA194SourceAllPreservation.lean | tee -a "$task_dir/axioms.log"
lean -M6000 -j1 -o "$task_dir/PA194SourceUniversalPreservation.olean" Computability/BusyBeaver/Research/PA/pa195-calibration/PA194SourceUniversalPreservation.lean | tee -a "$task_dir/axioms.log"
lean -M6000 -j1 -o "$task_dir/PA194SourceMPPreservation.olean" Computability/BusyBeaver/Research/PA/pa195-calibration/PA194SourceMPPreservation.lean | tee -a "$task_dir/axioms.log"
lean -M6000 -j1 Computability/BusyBeaver/Research/PA/pa195-calibration/PA194SourceLineSoundness.lean | tee -a "$task_dir/axioms.log"
if rg -q 'sorryAx' "$task_dir/axioms.log"; then
  echo 'Unexpected sorryAx in theorem dependencies' >&2
  exit 1
fi
