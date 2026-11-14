#!/usr/bin/env bash
set -euo pipefail

: "${IPRA_LEAN_OVERLAY:?Set IPRA_LEAN_OVERLAY to the built iPRA module directory}"
: "${IPRA_FOUNDATION_OVERLAY:?Set IPRA_FOUNDATION_OVERLAY to the built Foundation module directory}"
repo=$(git -C "$(dirname "$0")" rev-parse --show-toplevel)
cd "$repo"
IPRA_LEAN_OVERLAY=$(realpath "$IPRA_LEAN_OVERLAY")
IPRA_FOUNDATION_OVERLAY=$(realpath "$IPRA_FOUNDATION_OVERLAY")
sha256sum -c <<'PINS'
152d1d552b27baca8db0ac05b16092d9083c2ab979bb0b4e7f96a95803d9a9b0  Computability/BusyBeaver/Research/PA/jamesyc-upstream/pa196/M6/Zip.lean
842453bc52956492e439df8ccadbe00b1c0a2bac547d157b48b13daa045a8946  Computability/DiophantineConsistency/Lean/DiophantineConsistency/PRAHistoryPairCode.lean
a346cba7ed93b8d495eeca81c85e52510eb45938bf417eb950d9e66b2a0d2f98  Computability/DiophantineConsistency/Lean/DiophantineConsistency/PRAIsZero.lean
f0a5ba7482344477c2c7ca5ec2544f127ede62ec30e60b1101bfaed7be94db74  Computability/DiophantineConsistency/Lean/DiophantineConsistency/PRAFiniteFunctionCodes.lean
5e21edfdc4593f441f46f7fde9f8d0fc467eb1369c03251fe4f3a1a4d17a57de  Computability/DiophantineConsistency/Lean/DiophantineConsistency/PRALanguage.lean
2028e9ee96cbf335faaefd878d6cd177bd4ae7c469442977bded19da2e30a89d  Computability/DiophantineConsistency/Lean/DiophantineConsistency/PRAAddOne.lean
PINS
printf '%s  %s\n' \
  17b5937fcca095d4c3abb51a2e4cb51d7754eb7de1a31f87f8d62936065b3b77 "$IPRA_LEAN_OVERLAY/DiophantineConsistency/PRAHistoryPairCode.olean" \
  aae6176985ffcfadfb94c9681a816443ddd189f39a4a76a89a218c1d8cacb36c "$IPRA_LEAN_OVERLAY/DiophantineConsistency/PRAIsZero.olean" \
  d2e85d72099f9d869c9582aad5fb13079968d9d121ac6061e8326b00800b306e "$IPRA_FOUNDATION_OVERLAY/Init.olean" | sha256sum -c

sha256sum -c <<'PINS'
2cca9bfd32017c99456b4c1eb1fe07e8f7a343d5f1673082da9681a5d62903fe  Computability/DiophantineConsistency/Lean/DiophantineConsistency/IPRABoundedInduction.lean
8f05adbfe1c6978cab03ba2237788460db99fee3dcc51ce8d1185af2ca49b736  Computability/DiophantineConsistency/Lean/DiophantineConsistency/IPRAFullGGTransfer.lean
eda9313ff546c4913e100c86f273d550eac3f9be431482698d968c7ecacfa887  Computability/DiophantineConsistency/Lean/DiophantineConsistency/IPRANativeDisjunctionWitness.lean
c2800acbf0077a1c4d95707a6118e89d6d5cf6a3f9193139d5b2098411b4f120  Computability/DiophantineConsistency/Lean/DiophantineConsistency/IPRAStandardTheory.lean
PINS
printf '%s  %s\n' \
  a9c6d73ab1925c7f1a8ea2671d692a3798dd4bd1f3a8e68ee6d8daffc14099c4 "$IPRA_LEAN_OVERLAY/DiophantineConsistency/IPRABoundedInduction.olean" \
  7093a6af5d44b697e23fb2aba0458c570ea8339cef30dfdaefe51ceab55c4ac4 "$IPRA_LEAN_OVERLAY/DiophantineConsistency/IPRAFullGGTransfer.olean" \
  5ad8a1ef04ae3b5d691034ebd36e48884c0cbbaba3fdc229d8ef73695477315c "$IPRA_LEAN_OVERLAY/DiophantineConsistency/IPRANativeDisjunctionWitness.olean" \
  b2417583564a1d6b0bbfb4952587db79339fab8c2b4d24442145e39578173e19 "$IPRA_LEAN_OVERLAY/DiophantineConsistency/IPRAStandardTheory.olean" | sha256sum -c

sha256sum -c <<'PINS'
e66961d7acb60e0c84e9674ee2d91ca2049ac6d704ad0edf7d971ef933f3ce2e  Computability/BusyBeaver/Research/PA/jamesyc-upstream/pa196/M6/Runtime.lean
49ce05862aae65c8774af1f2a801b6e45789fc44cefb4c3b04501fb81749979c  Computability/DiophantineConsistency/Lean/DiophantineConsistency/PRATermCompilation.lean
PINS
printf '%s  %s\n' \
  0b3a10a1d85a6eb1d66a02ccd586021728a2aa6a156ee17dcf766a2e397d3cfd "$IPRA_LEAN_OVERLAY/DiophantineConsistency/PRATermCompilation.olean" | sha256sum -c

task_dir=$(mktemp -d "${TMPDIR:-/dev/shm}/binary-tape-code.XXXXXXXX")
trap 'rm -rf "$task_dir"' EXIT
mkdir -p "$task_dir/M6"
export BINARY_TAPE_TASK_DIR="$task_dir" IPRA_LEAN_OVERLAY IPRA_FOUNDATION_OVERLAY
python3 -B Computability/BusyBeaver/Research/PA/pa194/ipra/generate.py "$repo" "$task_dir"
lake env bash -c '
set -euo pipefail
lean --version | rg -q "Lean \(version 4\.32\.0"
export LEAN_PATH="$IPRA_LEAN_OVERLAY:$IPRA_FOUNDATION_OVERLAY:${LEAN_PATH:-}"
lean -M5000 -j1 Computability/BusyBeaver/Research/PA/pa194/ipra/machine-code/BinaryTapeCodes.lean \
  -o "$BINARY_TAPE_TASK_DIR/BinaryTapeCodes.olean" | tee "$BINARY_TAPE_TASK_DIR/axioms.log"
export LEAN_PATH="$BINARY_TAPE_TASK_DIR:$LEAN_PATH"
lean -M5000 -j1 Computability/BusyBeaver/Research/PA/pa194/ipra/machine-code/TapeStepCodes.lean \
  -o "$BINARY_TAPE_TASK_DIR/TapeStepCodes.olean" | tee -a "$BINARY_TAPE_TASK_DIR/axioms.log"
lean -R "$BINARY_TAPE_TASK_DIR" -M5000 -j1 "$BINARY_TAPE_TASK_DIR/PA194Rows.lean" \
  -o "$BINARY_TAPE_TASK_DIR/PA194Rows.olean"
lean -M5000 -j1 Computability/BusyBeaver/Research/PA/pa194/ipra/machine-code/TableDispatch.lean \
  -o "$BINARY_TAPE_TASK_DIR/TableDispatch.olean" | tee -a "$BINARY_TAPE_TASK_DIR/axioms.log"
lean -M5000 -j1 Computability/BusyBeaver/Research/PA/pa194/ipra/machine-code/TableModelSemantics.lean \
  -o "$BINARY_TAPE_TASK_DIR/TableModelSemantics.olean" | tee -a "$BINARY_TAPE_TASK_DIR/axioms.log"
lean -M5000 -j1 Computability/BusyBeaver/Research/PA/pa194/ipra/machine-code/ConfigurationStep.lean \
  -o "$BINARY_TAPE_TASK_DIR/ConfigurationStep.olean" | tee -a "$BINARY_TAPE_TASK_DIR/axioms.log"
lean -M6000 -j1 Computability/BusyBeaver/Research/PA/jamesyc-upstream/pa196/M6/Zip.lean \
  -o "$BINARY_TAPE_TASK_DIR/M6/Zip.olean"
lean -R "$BINARY_TAPE_TASK_DIR" -M6000 -j1 "$BINARY_TAPE_TASK_DIR/PA194Literal.lean" \
  -o "$BINARY_TAPE_TASK_DIR/PA194Literal.olean"
lean -M6000 -j1 Computability/BusyBeaver/Research/PA/pa194/ipra/PA194Bounded.lean \
  -o "$BINARY_TAPE_TASK_DIR/PA194Bounded.olean"
lean -M6000 -j1 Computability/BusyBeaver/Research/PA/pa194/ipra/machine-code/ConfigurationStandard.lean \
  -o "$BINARY_TAPE_TASK_DIR/ConfigurationStandard.olean" | tee -a "$BINARY_TAPE_TASK_DIR/axioms.log"
lean -M6000 -j1 Computability/BusyBeaver/Research/PA/pa194/ipra/machine-code/PackedClock.lean \
  -o "$BINARY_TAPE_TASK_DIR/PackedClock.olean" | tee -a "$BINARY_TAPE_TASK_DIR/axioms.log"
lean -M6000 -j1 Computability/BusyBeaver/Research/PA/pa194/ipra/machine-code/PackedStandard.lean \
  -o "$BINARY_TAPE_TASK_DIR/PackedStandard.olean" | tee -a "$BINARY_TAPE_TASK_DIR/axioms.log"
lean -M6000 -j1 Computability/BusyBeaver/Research/PA/pa194/ipra/machine-code/PackedRootModel.lean \
  -o "$BINARY_TAPE_TASK_DIR/PackedRootModel.olean" | tee -a "$BINARY_TAPE_TASK_DIR/axioms.log"
lean -M6000 -j1 Computability/BusyBeaver/Research/PA/pa194/ipra/machine-code/PackedDecoderModel.lean \
  -o "$BINARY_TAPE_TASK_DIR/PackedDecoderModel.olean" | tee -a "$BINARY_TAPE_TASK_DIR/axioms.log"
lean -M6000 -j1 Computability/BusyBeaver/Research/PA/pa194/ipra/machine-code/PackedIterationModel.lean \
  -o "$BINARY_TAPE_TASK_DIR/PackedIterationModel.olean" | tee -a "$BINARY_TAPE_TASK_DIR/axioms.log"
lean -M6000 -j1 Computability/BusyBeaver/Research/PA/pa194/ipra/machine-code/PA194FiniteControls.lean \
  -o "$BINARY_TAPE_TASK_DIR/PA194FiniteControls.olean" | tee -a "$BINARY_TAPE_TASK_DIR/axioms.log"
lean -M6000 -j1 Computability/BusyBeaver/Research/PA/pa194/ipra/machine-code/PA194LiteralStepModel.lean \
  -o "$BINARY_TAPE_TASK_DIR/PA194LiteralStepModel.olean" | tee -a "$BINARY_TAPE_TASK_DIR/axioms.log"
lean -M6000 -j1 Computability/BusyBeaver/Research/PA/pa194/ipra/machine-code/PA194Stepper.lean \
  -o "$BINARY_TAPE_TASK_DIR/PA194Stepper.olean" | tee -a "$BINARY_TAPE_TASK_DIR/axioms.log"
lean -M6000 -j1 Computability/BusyBeaver/Research/PA/pa194/ipra/machine-code/PA194RunLiteral.lean \
  -o "$BINARY_TAPE_TASK_DIR/PA194RunLiteral.olean" | tee -a "$BINARY_TAPE_TASK_DIR/axioms.log"
lean -M6000 -j1 Computability/BusyBeaver/Research/PA/pa194/ipra/machine-code/PA194BinaryDouble.lean \
  -o "$BINARY_TAPE_TASK_DIR/PA194BinaryDouble.olean" | tee -a "$BINARY_TAPE_TASK_DIR/axioms.log"
lean -M6000 -j1 Computability/BusyBeaver/Research/PA/pa194/ipra/machine-code/PA194StateOne.lean \
  -o "$BINARY_TAPE_TASK_DIR/PA194StateOne.olean" | tee -a "$BINARY_TAPE_TASK_DIR/axioms.log"
lean -M6000 -j1 Computability/BusyBeaver/Research/PA/pa194/ipra/machine-code/PA194UnaryRuns.lean \
  -o "$BINARY_TAPE_TASK_DIR/PA194UnaryRuns.olean" | tee -a "$BINARY_TAPE_TASK_DIR/axioms.log"
lean -M6000 -j1 Computability/BusyBeaver/Research/PA/pa194/ipra/machine-code/PA194ScanInvariant.lean \
  -o "$BINARY_TAPE_TASK_DIR/PA194ScanInvariant.olean" | tee -a "$BINARY_TAPE_TASK_DIR/axioms.log"
lean -M6000 -j1 Computability/BusyBeaver/Research/PA/pa194/ipra/machine-code/PA194StateFifteen.lean \
  -o "$BINARY_TAPE_TASK_DIR/PA194StateFifteen.olean" | tee -a "$BINARY_TAPE_TASK_DIR/axioms.log"
lean -M6000 -j1 Computability/BusyBeaver/Research/PA/pa194/ipra/machine-code/PA194ZeroRuns.lean \
  -o "$BINARY_TAPE_TASK_DIR/PA194ZeroRuns.olean" | tee -a "$BINARY_TAPE_TASK_DIR/axioms.log"
lean -M6000 -j1 Computability/BusyBeaver/Research/PA/pa194/ipra/machine-code/PA194ZeroScanInvariant.lean \
  -o "$BINARY_TAPE_TASK_DIR/PA194ZeroScanInvariant.olean" | tee -a "$BINARY_TAPE_TASK_DIR/axioms.log"
lean -M6000 -j1 Computability/BusyBeaver/Research/PA/pa194/ipra/machine-code/PRAEqualityToIPRA.lean \
  -o "$BINARY_TAPE_TASK_DIR/PRAEqualityToIPRA.olean" | tee -a "$BINARY_TAPE_TASK_DIR/axioms.log"
lean -M6000 -j1 Computability/BusyBeaver/Research/PA/pa194/ipra/machine-code/PA194NativeScans.lean \
  -o "$BINARY_TAPE_TASK_DIR/PA194NativeScans.olean" | tee -a "$BINARY_TAPE_TASK_DIR/axioms.log"
lean -M6000 -j1 Computability/BusyBeaver/Research/PA/pa194/ipra/machine-code/PA194StateTwelve.lean \
  -o "$BINARY_TAPE_TASK_DIR/PA194StateTwelve.olean" | tee -a "$BINARY_TAPE_TASK_DIR/axioms.log"
lean -M6000 -j1 Computability/BusyBeaver/Research/PA/pa194/ipra/machine-code/PA194TwelveTransition.lean \
  -o "$BINARY_TAPE_TASK_DIR/PA194TwelveTransition.olean" | tee -a "$BINARY_TAPE_TASK_DIR/axioms.log"
lean -M6000 -j1 Computability/BusyBeaver/Research/PA/pa194/ipra/machine-code/PA194TwelveScanInvariant.lean \
  -o "$BINARY_TAPE_TASK_DIR/PA194TwelveScanInvariant.olean" | tee -a "$BINARY_TAPE_TASK_DIR/axioms.log"
lean -M6000 -j1 Computability/BusyBeaver/Research/PA/pa194/ipra/machine-code/PA194TwelveNative.lean \
  -o "$BINARY_TAPE_TASK_DIR/PA194TwelveNative.olean" | tee -a "$BINARY_TAPE_TASK_DIR/axioms.log"
lean -M6000 -j1 Computability/BusyBeaver/Research/PA/pa194/ipra/machine-code/PA194StateTwelveExit.lean \
  -o "$BINARY_TAPE_TASK_DIR/PA194StateTwelveExit.olean" | tee -a "$BINARY_TAPE_TASK_DIR/axioms.log"
lean -M6000 -j1 Computability/BusyBeaver/Research/PA/pa194/ipra/machine-code/PA194TwelveExitComposition.lean \
  -o "$BINARY_TAPE_TASK_DIR/PA194TwelveExitComposition.olean" | tee -a "$BINARY_TAPE_TASK_DIR/axioms.log"
lean -M6000 -j1 Computability/BusyBeaver/Research/PA/pa194/ipra/machine-code/PA194TwelveExitSentence.lean \
  -o "$BINARY_TAPE_TASK_DIR/PA194TwelveExitSentence.olean" | tee -a "$BINARY_TAPE_TASK_DIR/axioms.log"
lean -M6000 -j1 Computability/BusyBeaver/Research/PA/pa194/ipra/machine-code/PA194StateThirteen.lean \
  -o "$BINARY_TAPE_TASK_DIR/PA194StateThirteen.olean" | tee -a "$BINARY_TAPE_TASK_DIR/axioms.log"
lean -M6000 -j1 Computability/BusyBeaver/Research/PA/pa194/ipra/machine-code/PA194ThirteenTransition.lean \
  -o "$BINARY_TAPE_TASK_DIR/PA194ThirteenTransition.olean" | tee -a "$BINARY_TAPE_TASK_DIR/axioms.log"
lean -M6000 -j1 Computability/BusyBeaver/Research/PA/pa194/ipra/machine-code/PA194ThirteenScanInvariant.lean \
  -o "$BINARY_TAPE_TASK_DIR/PA194ThirteenScanInvariant.olean" | tee -a "$BINARY_TAPE_TASK_DIR/axioms.log"
lean -M6000 -j1 Computability/BusyBeaver/Research/PA/pa194/ipra/machine-code/PA194ThirteenNative.lean \
  -o "$BINARY_TAPE_TASK_DIR/PA194ThirteenNative.olean" | tee -a "$BINARY_TAPE_TASK_DIR/axioms.log"
lean -M6000 -j1 Computability/BusyBeaver/Research/PA/pa194/ipra/machine-code/PA194StepperCompose.lean \
  -o "$BINARY_TAPE_TASK_DIR/PA194StepperCompose.olean" | tee -a "$BINARY_TAPE_TASK_DIR/axioms.log"
lean -M6000 -j1 Computability/BusyBeaver/Research/PA/pa194/ipra/machine-code/PA194TwelveThirteenCompose.lean \
  -o "$BINARY_TAPE_TASK_DIR/PA194TwelveThirteenCompose.olean" | tee -a "$BINARY_TAPE_TASK_DIR/axioms.log"
lean -M6000 -j1 Computability/BusyBeaver/Research/PA/pa194/ipra/machine-code/PA194TwelveThirteenSentence.lean \
  -o "$BINARY_TAPE_TASK_DIR/PA194TwelveThirteenSentence.olean" | tee -a "$BINARY_TAPE_TASK_DIR/axioms.log"
lean -M6000 -j1 Computability/BusyBeaver/Research/PA/jamesyc-upstream/pa196/M6/Runtime.lean \
  -o "$BINARY_TAPE_TASK_DIR/M6/Runtime.olean"
lean -M6000 -j1 Computability/BusyBeaver/Research/PA/pa194/ipra/machine-code/PA194RegisterFile.lean \
  -o "$BINARY_TAPE_TASK_DIR/PA194RegisterFile.olean" | tee -a "$BINARY_TAPE_TASK_DIR/axioms.log"
lean -M6000 -j1 Computability/BusyBeaver/Research/PA/pa194/ipra/machine-code/PA194RegisterFileStandard.lean \
  -o "$BINARY_TAPE_TASK_DIR/PA194RegisterFileStandard.olean" | tee -a "$BINARY_TAPE_TASK_DIR/axioms.log"
lean -M6000 -j1 Computability/BusyBeaver/Research/PA/pa194/ipra/machine-code/PA194RegisterFileHead.lean \
  -o "$BINARY_TAPE_TASK_DIR/PA194RegisterFileHead.olean" | tee -a "$BINARY_TAPE_TASK_DIR/axioms.log"
lean -M6000 -j1 Computability/BusyBeaver/Research/PA/pa194/ipra/machine-code/PA194RegisterEngine.lean \
  -o "$BINARY_TAPE_TASK_DIR/PA194RegisterEngine.olean" | tee -a "$BINARY_TAPE_TASK_DIR/axioms.log"
lean -M6000 -j1 Computability/BusyBeaver/Research/PA/pa194/ipra/machine-code/PA194RegisterEngineSentence.lean \
  -o "$BINARY_TAPE_TASK_DIR/PA194RegisterEngineSentence.olean" | tee -a "$BINARY_TAPE_TASK_DIR/axioms.log"
lean -M6000 -j1 Computability/BusyBeaver/Research/PA/pa194/ipra/machine-code/PA194StateTwo.lean \
  -o "$BINARY_TAPE_TASK_DIR/PA194StateTwo.olean" | tee -a "$BINARY_TAPE_TASK_DIR/axioms.log"
lean -M6000 -j1 Computability/BusyBeaver/Research/PA/pa194/ipra/machine-code/PA194StateZero.lean \
  -o "$BINARY_TAPE_TASK_DIR/PA194StateZero.olean" | tee -a "$BINARY_TAPE_TASK_DIR/axioms.log"
lean -M6000 -j1 Computability/BusyBeaver/Research/PA/pa194/ipra/machine-code/PA194SelectedEntry.lean \
  -o "$BINARY_TAPE_TASK_DIR/PA194SelectedEntry.olean" | tee -a "$BINARY_TAPE_TASK_DIR/axioms.log"
lean -M6000 -j1 Computability/BusyBeaver/Research/PA/pa194/ipra/machine-code/PA194SelectedCell.lean \
  -o "$BINARY_TAPE_TASK_DIR/PA194SelectedCell.olean" | tee -a "$BINARY_TAPE_TASK_DIR/axioms.log"
lean -M6000 -j1 Computability/BusyBeaver/Research/PA/pa194/ipra/machine-code/PA194SelectedCellSentence.lean \
  -o "$BINARY_TAPE_TASK_DIR/PA194SelectedCellSentence.olean" | tee -a "$BINARY_TAPE_TASK_DIR/axioms.log"
lean -M6000 -j1 Computability/BusyBeaver/Research/PA/pa194/ipra/machine-code/PA194MarkedFile.lean \
  -o "$BINARY_TAPE_TASK_DIR/PA194MarkedFile.olean" | tee -a "$BINARY_TAPE_TASK_DIR/axioms.log"
lean -M6000 -j1 Computability/BusyBeaver/Research/PA/pa194/ipra/machine-code/PA194MarkedFileStandard.lean \
  -o "$BINARY_TAPE_TASK_DIR/PA194MarkedFileStandard.olean" | tee -a "$BINARY_TAPE_TASK_DIR/axioms.log"
lean -M6000 -j1 Computability/BusyBeaver/Research/PA/pa194/ipra/machine-code/PA194MarkedFileSentence.lean \
  -o "$BINARY_TAPE_TASK_DIR/PA194MarkedFileSentence.olean" | tee -a "$BINARY_TAPE_TASK_DIR/axioms.log"
if rg -q "sorryAx" "$BINARY_TAPE_TASK_DIR/axioms.log"; then
  echo "Unexpected sorryAx in theorem dependencies" >&2
  exit 1
fi
'
