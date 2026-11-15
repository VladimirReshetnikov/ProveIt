#!/usr/bin/env bash
set -euo pipefail
if (($# != 10)); then
  echo "usage: $0 REPO SOURCE_DIR CONTROLLER_SOURCE_DIR BRIDGE_SOURCE_DIR ZERO_SOURCE_DIR SITE27_BASELINE CODE_GRAPH_OVERLAY PROJECT_FOUNDATION PACKAGE_FOUNDATION CLOCK_SOURCE_DIR" >&2
  exit 2
fi
repo=$(realpath "$1")
source=$(realpath "$2")
controller=$(realpath "$3")
bridge=$(realpath "$4")
zerosrc=$(realpath "$5")
baseline=$(realpath "$6")
graph=$(realpath "$7")
project=$(realpath "$8")
package=$(realpath "$9")
clocksrc=$(realpath "${10}")
for v in GIT_DIR GIT_WORK_TREE GIT_INDEX_FILE GIT_OBJECT_DIRECTORY GIT_ALTERNATE_OBJECT_DIRECTORIES; do
  if [[ -v "$v" ]]; then echo "Refusing inherited $v" >&2; exit 2; fi
done
printf '%s  %s\n' \
  c9f6f2d566b34f78dfe838fcba1537f06fdac7ed92925adb487b57046ee7e5ba "$clocksrc/PA194Site27ZeroExactClock.lean" \
  770060b4a38ceaa62ccbbfa96fd3f0879d5fc6763a12bfed2a871d745ed2de9a "$clocksrc/PA194Site27ZeroClockPhysical.lean" \
  9a7d34bcc9d3fe5f98a40c36bbd3e9d8eef3a1eb029abbea483fa69efcf56872 "$source/PA194ConditionalModelLength.lean" \
  e80bebe51d09ff1f74b1205db992d82e050ce0aa2c26e5a0f5656add84ff48b4 "$source/PA194CumulativeClock.lean" \
  cb222585a8a00789886393046065e49abb070f28ed15b289e39cbac4362c5d72 "$source/PA194ClockInvariantDefinable.lean" \
  179fe8da3dcb74ef7050ded0172ce8f5934c27db9dec8bd8c56739c9c4d4222a "$source/PA194ClockedSimulation.lean" \
  11154b2bc52066d049b22fa2a7ad65ffa7055b8bfe81ad7ae73be14e6bd726e6 "$source/PA194IteratedSimulation.lean" \
  809c7111d09354deb92b4deb4f1e5cde2ab4e20334ef8237f8b731d93f88a2d4 "$controller/PA194SourceControllerCode.lean" \
  345884236856b4dec5666513e8d03e3c1ff412f006731d0cc6f9e2b17886f911 "$controller/PA194SourceControllerBinding.lean" \
  35ccd5b8cd38c9cccbd50c424f92888a7f9edeeced293fb92774b83f8bc0d65b "$controller/PA194SourceRegisters.lean" \
  f3510ac5eb8b39a6e92dffff419e0193f5004e07772a3675235f5d9936f86a4a "$controller/PA194SourceControllerSites.lean" \
  5b3162125b86e2f05662ff390c8e087b738e06df34a2245771511f1b9db4aa79 "$controller/PA194SourceInstructionModel.lean" \
  4d4552509fdf0841dec0581fb105ca63dfa6ab501551d6ab1023ec39c763bd80 "$controller/PA194SourceControllerStep.lean" \
  cca3656c1cf5ffa9b1664d81ea7c7e007dd2fe06e87bfd7b826e68ae4613755c "$controller/PA194SourceRegisterRelation.lean" \
  36e787b2be95d47e18d7ff2db8bdc1cac379e26d33e3d86823922dd7266f623a "$controller/PA194SourceInstructionCalibration.lean" \
  3355e65dfa4418d0a2461204ef73425fd2b53eb128fee6db81518cec532494c5 "$controller/PA194SourceActualStepCalibration.lean" \
  bab05af23b65ce767963fe809637baf6653701e9124f20192126067e45e2b159 "$controller/PA194SourceBoundedStep.lean" \
  0eac85d196701db8ddcdea84c86e3104fb60333621e2d107c82c99da3613c7f4 "$controller/PA194SourceTargetBounds.lean" \
  ee722a26f0e7beabf79161244b0be53bd45d5f5551c48b24e96f2fd74f11041b "$controller/PA194SourcePCBound.lean" \
  f5b245c51e3f47c3dd4088277099484605c282e50e8e6080b128a34e5413cbe3 "$bridge/PA194SourceSite25Physical.lean" \
  f86c0660193f81c54c5d30b84580dbabba2ed87c0124535d4da077b3eb14cd33 "$bridge/PA194SourceSite25Positive.lean" \
  bcb5c0017f295ae1dbc6e9b7187728434f11e79c7e1435b1f7da1023f600dc58 "$zerosrc/PA194Site27ZeroTo5.lean" \
  166cab82c4b37cb25f070dc00f476498a3f5f75ab12922b73b75013703a19ff8 "$zerosrc/PA194Site27ZeroTo11.lean" \
  09de5a72822bf08fd7f2d68bb69af001ce37b93681f3a4d3d66292a45cc668f0 "$zerosrc/PA194Site27ZeroExact.lean" \
  319a6ac268f89699023929a9398bd61153310f6329072c31d8c81c95f2e5496c "$zerosrc/PA194CarryAppendZero.lean" \
  44ec0c4efcbe1127fd6bf1d21a279c5d1fd83621e4955799dc3d0e17c97e435c "$zerosrc/PA194Site27ZeroRollback.lean" \
  001c491d29dc387e38a54caf8667669ced54420e520a72baa3bc430b2fd6a6ab "$baseline/PA194RollbackFile.olean" \
  b943682758dd3924468c7a681ff21cf6c9f460b44408533d9da0144256835dbe "$baseline/PA194CarryFile.olean" \
  bfc365fd528ad022eef21613c30d25b615e95e7472ea567a005cff02904e435d "$zerosrc/PA194Site27ZeroTo12.lean" \
  1f66b14680986f5f99d5c0bb141acdc59df15d068a068e8f75e3dbb2208032bc "$zerosrc/PA194Site27ZeroTo14.lean" \
  7823f32246339f0ba1a60d25b5da1ee95866d73bd15a8292ebc5aa3a7e74b2ea "$baseline/PA194ZeroReturnTo12.olean" \
  ebbbb95cb02b5aa648223f38be447a756b2f865cb0634ffa1fb72d3dc768a1a9 "$baseline/PA194ThirteenExitComposition.olean" \
  70cb1e6fba93d0c8beaa2ffb1591fb22a7e199e89d411777e6293f33a88ac1a7 "$baseline/PA194HeaderController.olean" \
  d1568228f12ecf2c437381f660c92da1de2d6e7c79e4733430907afd4a978f2c "$zerosrc/PA194Site27ZeroTo24.lean" \
  c9943b61a418fedc958960b940752587ae476702ae51facc55e4b4d93eb81ce4 "$baseline/PA194ZeroReturnTo16.olean" \
  d32e0974c9cbada03686bcd5b0b138c7aec2debe4491cfee12f966f201fbfefd "$baseline/PA194ZeroReturnFrom16.olean" \
  dc3a99072faa1338c896278f3a667a00814d33ee882c42b3b4ac526bf361f145 "$baseline/PA194LeftOneWriteOne.olean" \
  101767c63cbf4a11b9ad23f201f1be27a9bc8681a8fa12d155f7d032b40926ff "$zerosrc/PA194Site27ZeroFile.lean" \
  95d26c326cac59eb185413d7f3c0da2f85e5de983d663e525f76160c9d200327 "$zerosrc/PA194Path31Header.lean" \
  64ee17ac48eb16776a733f81b7743b0dbc89fb017aa137e1ec7b7bcafc219d00 "$zerosrc/PA194Site27ZeroPath.lean" \
  64d4a80a8e723ea8c01df389230c5ca437a9faa3f5932459dbce77687c458225 "$zerosrc/PA194SourceSite27Zero.lean" \
  d0eafa9cc090cfbff9d7ccad06cdd1bde91f92f5c2cf05784d5df08b90ec9c2d "$bridge/PA194Site25FrameRelation.lean" \
  bb59f1fbaf7d97e8512ecf3e4efc71c28e1b210d421817b4e218109cf964891c "$bridge/PA194SourceSite27Physical.lean" \
  72b392c77ea0bc7cc4bf0012fd9aa161ca79458c4e8558363708dd4de679b388 "$repo/Computability/BusyBeaver/Research/PA/pa194/ipra/machine-code/PA194Path27To28.lean" \
  c4aef4576f072a828247a9d934260cce89302bf31bcfc0aa2d2f48963f4cbcd2 "$baseline/PA194Path27Header.olean" \
  315904d667a59784df70e9fdc8ab40bd4ae7198956e5aedfe857f41a6b1013a6 "$baseline/PA194ReturnFileMeaning.olean" \
  83a9fe37590a9c232f0392cc5ecd3ac44cd0b4579215749649d071604e3927bc "$baseline/PA194Site27To4.olean" \
  030d732e6be8818dbaf340f52f6addf7ef9958754994e6cb5d92f61094f4e933 "$baseline/PA194Site27BranchRows.olean" \
  000a2102248cfd4f1761903685c9095219b43eff9f863b50f024fb7427816079 "$baseline/PA194Path27Input.olean" \
  937275cc570a2a619286eb982a9ec2b40987ea993ee2b8a5b86ed5a3d2a34adf "$baseline/PA194DecrementZeroCell.olean" \
  d569cc4723e2c87b80534f9aadf810d22df5fb70afc1aec615e4e245a95e7cbf "$bridge/physical-baseline-receipt.json" \
  6d34ca8f62b040c0c1c4b0a83c10370aaf28edb029e5e998274e187032e0b543 "$baseline/site27-coherent-manifest.json" \
  4da56e9178bdb0950df59671d505fde659bb2f709aaecf0a108231bdfa18ba6a "$repo/Computability/BusyBeaver/Research/PA/pa194/ipra/machine-code/PA194Site27PathStep.lean" \
  69044b06d8b83ad8562a76af549df11391d936ebfb87b9f0b1ba2963b7301ed0 "$repo/Computability/BusyBeaver/Research/PA/pa194/ipra/machine-code/PA194Path25To27.lean" \
  064e4dacfa11962fdb8f2048b84511551747c804ca14daffaa7c640a24d197d3 "$baseline/PA194SourceProgram.olean" \
  ccdda76223212b8b4ece429a92d2c835b7a728211492739ca427a1f11ebbcfe5 "$baseline/PA194SourceTree.olean" \
  5861390d138991912d3e1c74bac804b39068bb2f3481a896d4d63bf10d576c2a "$baseline/PackedDecoderModel.olean" \
  06bf36b979a3a8d785b0939d4bb27a1c44c5742e4c0284a474ef781ac7bdb1a2 "$baseline/PA194StateOne.olean" \
  bda83078dd5c449e44777389898e46a9a7885013c8a4c6551d88a32161547c65 "$graph/DiophantineConsistency/PRAEqualityCode.olean" \
  d804c0fdbc8bd885d553665d8c0e3a671f0dc4db4001680f9223eb86b0c9b944 "$baseline/unified-coherent-manifest.json" \
  8b23b791247e4fb374ee0115773c59db0bd4eede5c3a14a4728758e3b6070778 "$baseline/PA194StepperCompose.olean" \
  7aa72b74a53bdc78cecc68fca7eee8192e6f556fe91c8cf4cadb899edadeb0d8 "$baseline/PA194Stepper.olean" \
  6167e5a2f0474023ec16588877f5b3abf1394efbbdaa0f388d9e0fea917c5ae2 "$graph/PA194CodeGraph.olean" \
  fbdf4fe0e3e66cce18d31e8bae714b47147633cc3295ad85ad50fd4194d28e64 "$graph/PA194ParamComp.olean" \
  703b246d062915d3d819d970aa66147219d796aa8517a6421f238ea3cc9db257 "$graph/PA194ParamRecursionDefined.olean" \
  2654808e5cfba0266f38ce2ddad33987635e8e06c3934cc131eb2a475bc1eeae "$graph/DiophantineConsistency/PRAHistoryResultGraph.olean" \
  bdfeb2a5aa83198a61c345ccb137a8bf99ef9fc23bccc7f6fc96a1d3295eb094 "$repo/Computability/BusyBeaver/Research/PA/pa195-work/pa195-calibration/PA194CodeGraph.lean" | sha256sum -c -
python3 - "$bridge/physical-baseline-receipt.json" "$baseline" <<'PYTHON'
import hashlib,json,sys
from pathlib import Path
receipt=json.loads(Path(sys.argv[1]).read_text()); root=Path(sys.argv[2])
for name,expected in receipt.items():
    path=root/(name+'.olean')
    actual=hashlib.sha256(path.read_bytes()).hexdigest()
    if actual != expected: raise SystemExit(f'baseline object mismatch: {path}')
print('Physical baseline direct objects:',len(receipt),'OK')
PYTHON
task_dir=$(mktemp -d "${TMPDIR:-/dev/shm}/pa194-site27-zero-prefix.XXXXXXXX")
trap 'rm -rf "$task_dir"' EXIT
cd "$repo"
lake_path=$(lake env printenv LEAN_PATH)
export LEAN_PATH="$task_dir:$baseline:$graph:$project:$package:$lake_path"
for m in PA194ConditionalModelLength PA194CumulativeClock PA194ClockInvariantDefinable PA194ClockedSimulation PA194IteratedSimulation PA194SourceControllerCode PA194SourceControllerBinding PA194SourceRegisters PA194SourceControllerSites PA194SourceInstructionModel PA194SourceControllerStep PA194SourceRegisterRelation PA194SourceInstructionCalibration PA194SourceActualStepCalibration PA194SourceBoundedStep PA194SourceTargetBounds PA194SourcePCBound; do
  case "$m" in
    PA194SourceControllerCode|PA194SourceControllerBinding|PA194SourceRegisters|PA194SourceControllerSites|PA194SourceInstructionModel|PA194SourceControllerStep|PA194SourceRegisterRelation|PA194SourceInstructionCalibration|PA194SourceActualStepCalibration|PA194SourceBoundedStep|PA194SourceTargetBounds|PA194SourcePCBound) cp "$controller/$m.lean" "$task_dir/$m.lean" ;;
    *) cp "$source/$m.lean" "$task_dir/$m.lean" ;;
  esac
  echo "Checking $m"
  lake env env LEAN_PATH="$LEAN_PATH" lean -R "$task_dir" -o "$task_dir/$m.olean" "$task_dir/$m.lean" 2>&1 | tee "$task_dir/$m.log"
  if rg -q 'sorryAx' "$task_dir/$m.log"; then echo 'Unexpected sorryAx' >&2; exit 1; fi
done
for spec in 'PA194ConditionalModelLength:simulateModelLength' 'PA194CumulativeClock:clockZero' 'PA194CumulativeClock:clockSucc' 'PA194ClockInvariantDefinable:invariantDef' 'PA194ClockedSimulation:simulateCodeRun' 'PA194SourceControllerBinding:ordinalTest' 'PA194SourceControllerBinding:dispatchAt' 'PA194SourceControllerBinding:selectActual' 'PA194SourceRegisters:getAuxModel' 'PA194SourceRegisters:putAuxModel' 'PA194SourceRegisters:readAfterWrite' 'PA194SourceRegisters:readOtherAfterWrite' 'PA194SourceControllerSites:site10Instruction' 'PA194SourceControllerSites:site25Instruction' 'PA194SourceControllerSites:selectSite10' 'PA194SourceControllerSites:selectSite25' 'PA194SourceInstructionModel:instructionModel' 'PA194SourceControllerStep:actualInstructionStep' 'PA194SourceControllerStep:site10Step' 'PA194SourceControllerStep:site25Zero' 'PA194SourceControllerStep:site25Positive' 'PA194SourceRegisterRelation:packEncodes' 'PA194SourceRegisterRelation:updateEncodes' 'PA194SourceInstructionCalibration:instructionCalibration' 'PA194SourceActualStepCalibration:actualStepCalibration' 'PA194SourceBoundedStep:boundedStepCalibration' 'PA194SourceTargetBounds:literalInstructionBound' 'PA194SourcePCBound:stepWorkingPCBound'; do
  module=${spec%%:*}; thm=${spec#*:}
  rg -q "^'$module\.$thm' depends on axioms:" "$task_dir/$module.log"
done
for m in PA194Site27PathStep PA194Path25To27 PA194SourceSite25Physical PA194SourceSite25Positive; do
  case "$m" in
    PA194Site27PathStep|PA194Path25To27) cp "$repo/Computability/BusyBeaver/Research/PA/pa194/ipra/machine-code/$m.lean" "$task_dir/$m.lean" ;;
    *) cp "$bridge/$m.lean" "$task_dir/$m.lean" ;;
  esac
  echo "Checking $m"
  lake env env LEAN_PATH="$LEAN_PATH" lean -j1 -R "$task_dir" -o "$task_dir/$m.olean" "$task_dir/$m.lean" 2>&1 | tee "$task_dir/$m.log"
  if rg -q 'sorryAx' "$task_dir/$m.log"; then echo 'Unexpected sorryAx' >&2; exit 1; fi
done
rg -q "^'PA194SourceSite25Physical.zeroBranch' depends on axioms:" "$task_dir/PA194SourceSite25Physical.log"
rg -q "^'PA194SourceSite25Positive.positiveBranch' depends on axioms:" "$task_dir/PA194SourceSite25Positive.log"
rg -q "^'PA194SourceSite25Positive.updateRegister8' depends on axioms:" "$task_dir/PA194SourceSite25Positive.log"
for m in PA194Site27ZeroTo5 PA194Site27ZeroTo11 PA194Site27ZeroExact PA194CarryAppendZero PA194Site27ZeroRollback PA194Site27ZeroTo12 PA194Site27ZeroTo14 PA194Site27ZeroTo24; do
  cp "$zerosrc/$m.lean" "$task_dir/$m.lean"
  echo "Checking $m"
  lake env env LEAN_PATH="$LEAN_PATH" lean -j1 -R "$task_dir" -o "$task_dir/$m.olean" "$task_dir/$m.lean" 2>&1 | tee "$task_dir/$m.log"
  if rg -q 'sorryAx' "$task_dir/$m.log"; then echo 'Unexpected sorryAx' >&2; exit 1; fi
done
rg -q "^'PA194Site27ZeroTo5.zeroTo5' depends on axioms:" "$task_dir/PA194Site27ZeroTo5.log"
rg -q "^'PA194Site27ZeroTo11.fiveTo11' depends on axioms:" "$task_dir/PA194Site27ZeroTo11.log"
rg -q "^'PA194Site27ZeroTo11.zeroTo11' depends on axioms:" "$task_dir/PA194Site27ZeroTo11.log"
for spec in PA194Site27ZeroExact:zeroTo5Exact PA194Site27ZeroExact:zeroTo11Exact PA194CarryAppendZero:sixThenZero PA194Site27ZeroRollback:carriedIsSeven PA194Site27ZeroRollback:zeroRollback PA194Site27ZeroTo12:zeroTo12 PA194Site27ZeroTo14:returnedEven PA194Site27ZeroTo14:zeroTo14 PA194Site27ZeroTo24:oneFrom16 PA194Site27ZeroTo24:zeroTo24; do
  module=${spec%%:*}; thm=${spec#*:}
  rg -q "^'$module\.$thm' depends on axioms:" "$task_dir/$module.log"
done
for m in PA194Site25FrameRelation PA194Path27To28 PA194SourceSite27Physical; do
  case "$m" in
    PA194Path27To28) cp "$repo/Computability/BusyBeaver/Research/PA/pa194/ipra/machine-code/$m.lean" "$task_dir/$m.lean" ;;
    *) cp "$bridge/$m.lean" "$task_dir/$m.lean" ;;
  esac
  echo "Checking $m"
  lake env env LEAN_PATH="$LEAN_PATH" lean -j1 -R "$task_dir" -o "$task_dir/$m.olean" "$task_dir/$m.lean" 2>&1 | tee "$task_dir/$m.log"
  if rg -q 'sorryAx' "$task_dir/$m.log"; then echo 'Unexpected sorryAx' >&2; exit 1; fi
done
for m in PA194Site27ZeroFile PA194Path31Header PA194Site27ZeroPath PA194SourceSite27Zero; do
  cp "$zerosrc/$m.lean" "$task_dir/$m.lean"
  echo "Checking $m"
  lake env env LEAN_PATH="$LEAN_PATH" lean -j1 -R "$task_dir" -o "$task_dir/$m.olean" "$task_dir/$m.lean" 2>&1 | tee "$task_dir/$m.log"
  if rg -q 'sorryAx' "$task_dir/$m.log"; then echo 'Unexpected sorryAx' >&2; exit 1; fi
done
for spec in PA194Site25FrameRelation:site25Step PA194Path27To28:positiveBranchPath27To28 PA194SourceSite27Physical:site27Instruction PA194SourceSite27Physical:positiveBranch PA194Site27ZeroFile:returnedIsSourceFile PA194Path31Header:path31 PA194Path31Header:path31Word PA194Site27ZeroPath:zeroBranchWithFile PA194SourceSite27Zero:zeroBranch PA194SourceSite27Zero:matchedStep; do
  module=${spec%%:*}; thm=${spec#*:}
  rg -q "^'$module\.$thm' depends on axioms:" "$task_dir/$module.log"
done
echo 'PASS: model-uniform actual site-27 controller and physical frame agree for both branches; general simulation remains open.'    

for m in PA194Site27ZeroExactClock PA194Site27ZeroClockPhysical; do
  cp "$clocksrc/$m.lean" "$task_dir/$m.lean"
  echo "Checking $m"
  lake env env LEAN_PATH="$LEAN_PATH" lean -M6000 -j1 -R "$task_dir" -o "$task_dir/$m.olean" "$task_dir/$m.lean" 2>&1 | tee "$task_dir/$m.log"
  if rg -q 'sorryAx' "$task_dir/$m.log"; then echo 'Unexpected sorryAx' >&2; exit 1; fi
done
for spec in PA194Site27ZeroExactClock:zeroTo5Exact PA194Site27ZeroExactClock:zeroTo11Exact PA194Site27ZeroClockPhysical:zeroRollback PA194Site27ZeroClockPhysical:zeroTo12 PA194Site27ZeroClockPhysical:zeroTo14 PA194Site27ZeroClockPhysical:zeroTo24 PA194Site27ZeroClockPhysical:zeroBranchWithFile; do
  module=${spec%%:*}; thm=${spec#*:}
  rg -q "^'$module\.$thm' depends on axioms:" "$task_dir/$module.log"
done
printf '%s  %s\n' \
  c9f6f2d566b34f78dfe838fcba1537f06fdac7ed92925adb487b57046ee7e5ba "$clocksrc/PA194Site27ZeroExactClock.lean" \
  770060b4a38ceaa62ccbbfa96fd3f0879d5fc6763a12bfed2a871d745ed2de9a "$clocksrc/PA194Site27ZeroClockPhysical.lean" \
  | sha256sum -c -
echo 'PASS: exact model clock for physical site-27 zero branch; staged machine/foundation roots remain prebuilt.'
