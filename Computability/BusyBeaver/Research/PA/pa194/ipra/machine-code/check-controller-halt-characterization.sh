#!/usr/bin/env bash
set -euo pipefail
if (($# != 8)); then
  echo "usage: $0 REPO SOURCE_DIR CONTROLLER_SOURCE_DIR UNIFIED_BASELINE CODE_GRAPH_OVERLAY PROJECT_FOUNDATION PACKAGE_FOUNDATION HALT_SOURCE_DIR" >&2
  exit 2
fi
repo=$(realpath "$1")
source=$(realpath "$2")
controller=$(realpath "$3")
baseline=$(realpath "$4")
graph=$(realpath "$5")
project=$(realpath "$6")
package=$(realpath "$7")
haltsrc=$(realpath "$8")
for v in GIT_DIR GIT_WORK_TREE GIT_INDEX_FILE GIT_OBJECT_DIRECTORY GIT_ALTERNATE_OBJECT_DIRECTORIES; do
  if [[ -v "$v" ]]; then echo "Refusing inherited $v" >&2; exit 2; fi
done
printf '%s  %s\n' \
  f09a57af4cff35380076930cde826a65bad6431c7cb9ff5441fcbe2eca71ce12 "$haltsrc/PA194SourceHaltUnique.lean" \
  e157a4e1aaba69ae917a1bb2862ef1cdb8817efe43664070a292e80145d3302c "$haltsrc/PA194ControllerHaltCharacterization.lean" \
  5991cd79d7c10596a27deed94c7b4aae9ccdd9010fa4226e76a92380bd9b9b38 "$haltsrc/PA194ControllerHaltRun.lean" \
  9054a253d607950b9946d04526ab40eceaac020a7e0690c7da12f0abbb520024 "$source/PA194SourceHaltSite.lean" \
  54ef8d68d165f2a2b98edff5662d86053d203091e4bbd19b1c4fe6b39949aa7e "$repo/Computability/BusyBeaver/Research/PA/pa194-work/pa194-source-tree/generate.py" \
  664befae8fdc26dc86ce229a4efb0da7210a5be89d9490b74d5e96c9be75e0ce "$repo/Computability/BusyBeaver/Research/PA/pa194-work/pa194-coverage/PA194SourceProgram.lean" \
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
  96b5e7213a9b4825d65bac8ba6de5085a846ea9b27e7068f7a57dd5b5f16ba2a "$controller/PA194SourceSentinel.lean" \
  a437ade95c50d6f73624d7980d7f7524c12c2deccc4c2831e55b50a99f2a06e8 "$controller/PA194SourceReachable.lean" \
  deefab41fec02a64445af9a1020f39bb3252da852cf18bc3a03a8854dec1ab50 "$controller/PA194SourceNoMalformed.lean" \
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
  bdfeb2a5aa83198a61c345ccb137a8bf99ef9fc23bccc7f6fc96a1d3295eb094 "$repo/Computability/BusyBeaver/Research/PA/other-machines/pa195-work/pa195-calibration/PA194CodeGraph.lean" | sha256sum -c -
task_dir=$(mktemp -d "${TMPDIR:-/dev/shm}/pa194-source-no-malformed.XXXXXXXX")
trap 'rm -rf "$task_dir"' EXIT
cd "$repo"
python3 "$repo/Computability/BusyBeaver/Research/PA/pa194-work/pa194-source-tree/generate.py" "$task_dir/PA194SourceTree.lean"
printf '%s  %s\n' 69f6dee4807f25ed36923a86b87c20bc23432bdaf43bf8a41148f76f05540ca1 "$task_dir/PA194SourceTree.lean" | sha256sum -c -
python3 - "$repo" <<'PYTHON'
import hashlib,sys
from pathlib import Path
root=Path(sys.argv[1]); sys.path.insert(0,str(root/'Computability/BusyBeaver/Research/PA'))
from packet_inputs import PlacedPacket
with PlacedPacket(root,'194') as p:
    b=p.read('pa194_conpa/construction/tables/pa194.tm')
assert hashlib.sha256(b).hexdigest()=='4bfea62b17aad7d8c8c5e682fe8942e0a86b93e4351f8e675e32705bdaae007f'
print('Pinned literal table hash: OK; source/physical correspondence is a separate obligation')
PYTHON
cp "$repo/Computability/BusyBeaver/Research/PA/pa194-work/pa194-coverage/PA194SourceProgram.lean" "$task_dir/PA194SourceProgram.lean"
cp "$source/PA194SourceHaltSite.lean" "$task_dir/PA194SourceHaltSite.lean"
lake_path=$(lake env printenv LEAN_PATH)
export LEAN_PATH="$task_dir:$baseline:$graph:$project:$package:$lake_path"
for m in PA194SourceTree PA194SourceProgram PA194SourceHaltSite; do
  echo "Checking $m"
  lake env env LEAN_PATH="$LEAN_PATH" lean -j1 -R "$task_dir" -o "$task_dir/$m.olean" "$task_dir/$m.lean" 2>&1 | tee "$task_dir/$m.log"
  if rg -q 'sorryAx' "$task_dir/$m.log"; then echo 'Unexpected sorryAx' >&2; exit 1; fi
done
for m in PA194ConditionalModelLength PA194CumulativeClock PA194ClockInvariantDefinable PA194ClockedSimulation PA194IteratedSimulation PA194SourceControllerCode PA194SourceControllerBinding PA194SourceRegisters PA194SourceControllerSites PA194SourceInstructionModel PA194SourceControllerStep PA194SourceRegisterRelation PA194SourceInstructionCalibration PA194SourceActualStepCalibration PA194SourceBoundedStep PA194SourceTargetBounds PA194SourcePCBound PA194SourceSentinel PA194SourceReachable PA194SourceNoMalformed; do
  case "$m" in
    PA194SourceControllerCode|PA194SourceControllerBinding|PA194SourceRegisters|PA194SourceControllerSites|PA194SourceInstructionModel|PA194SourceControllerStep|PA194SourceRegisterRelation|PA194SourceInstructionCalibration|PA194SourceActualStepCalibration|PA194SourceBoundedStep|PA194SourceTargetBounds|PA194SourcePCBound|PA194SourceSentinel|PA194SourceReachable|PA194SourceNoMalformed) cp "$controller/$m.lean" "$task_dir/$m.lean" ;;
    *) cp "$source/$m.lean" "$task_dir/$m.lean" ;;
  esac
  echo "Checking $m"
  lake env env LEAN_PATH="$LEAN_PATH" lean -R "$task_dir" -o "$task_dir/$m.olean" "$task_dir/$m.lean" 2>&1 | tee "$task_dir/$m.log"
  if rg -q 'sorryAx' "$task_dir/$m.log"; then echo 'Unexpected sorryAx' >&2; exit 1; fi
done
for spec in 'PA194ConditionalModelLength:simulateModelLength' 'PA194CumulativeClock:clockZero' 'PA194CumulativeClock:clockSucc' 'PA194ClockInvariantDefinable:invariantDef' 'PA194ClockedSimulation:simulateCodeRun' 'PA194SourceControllerBinding:ordinalTest' 'PA194SourceControllerBinding:dispatchAt' 'PA194SourceControllerBinding:selectActual' 'PA194SourceRegisters:getAuxModel' 'PA194SourceRegisters:putAuxModel' 'PA194SourceRegisters:readAfterWrite' 'PA194SourceRegisters:readOtherAfterWrite' 'PA194SourceControllerSites:site10Instruction' 'PA194SourceControllerSites:site25Instruction' 'PA194SourceControllerSites:selectSite10' 'PA194SourceControllerSites:selectSite25' 'PA194SourceInstructionModel:instructionModel' 'PA194SourceControllerStep:actualInstructionStep' 'PA194SourceControllerStep:site10Step' 'PA194SourceControllerStep:site25Zero' 'PA194SourceControllerStep:site25Positive' 'PA194SourceRegisterRelation:packEncodes' 'PA194SourceRegisterRelation:updateEncodes' 'PA194SourceInstructionCalibration:instructionCalibration' 'PA194SourceActualStepCalibration:actualStepCalibration' 'PA194SourceBoundedStep:boundedStepCalibration' 'PA194SourceTargetBounds:literalInstructionBound' 'PA194SourcePCBound:stepWorkingPCBound' 'PA194SourceSentinel:stepMalformed' 'PA194SourceSentinel:stepHalted' 'PA194SourceReachable:stepPCBound' 'PA194SourceReachable:runPCBound' 'PA194SourceNoMalformed:stepWorkingOrHalt' 'PA194SourceNoMalformed:stepValidPC' 'PA194SourceNoMalformed:runValidPC'; do
  module=${spec%%:*}; thm=${spec#*:}
  rg -q "^'$module\.$thm' depends on axioms:" "$task_dir/$module.log"
done
for m in PA194SourceHaltUnique PA194ControllerHaltCharacterization PA194ControllerHaltRun; do
  cp "$haltsrc/$m.lean" "$task_dir/$m.lean"
  echo "Checking $m"
  lake env env LEAN_PATH="$LEAN_PATH" lean -j1 -R "$task_dir" -o "$task_dir/$m.olean" "$task_dir/$m.lean" 2>&1 | tee "$task_dir/$m.log"
  if rg -q 'sorryAx' "$task_dir/$m.log"; then echo 'Unexpected sorryAx' >&2; exit 1; fi
done
for spec in PA194SourceHaltSite:uniqueHaltLeaf PA194SourceHaltUnique:resolvedHaltIndex PA194ControllerHaltCharacterization:executeHaltOnly PA194ControllerHaltCharacterization:nextHaltIffSite10 PA194ControllerHaltRun:nextHaltValid PA194ControllerHaltRun:runSuccessorHalt; do
  module=${spec%%:*}; thm=${spec#*:}
  rg -q "^'$module\.$thm' depends on axioms:" "$task_dir/$module.log"
done
echo 'PASS: actual source controller halt transition characterized at site 10; scheduler and physical simulation remain separate.' 
