#!/usr/bin/env bash
set -euo pipefail
if (($# != 9)); then
  echo "usage: $0 REPO SOURCE_DIR CONTROLLER_SOURCE_DIR UNIFIED_BASELINE CODE_GRAPH_OVERLAY PROJECT_FOUNDATION PACKAGE_FOUNDATION SCHEDULER_SOURCE_DIR SCHEDULER_PREBUILT_OVERLAY" >&2
  exit 2
fi
repo=$(realpath "$1")
source=$(realpath "$2")
controller=$(realpath "$3")
baseline=$(realpath "$4")
graph=$(realpath "$5")
project=$(realpath "$6")
package=$(realpath "$7")
schedsrc=$(realpath "$8")
schedbase=$(realpath "$9")
for v in GIT_DIR GIT_WORK_TREE GIT_INDEX_FILE GIT_OBJECT_DIRECTORY GIT_ALTERNATE_OBJECT_DIRECTORIES; do
  if [[ -v "$v" ]]; then echo "Refusing inherited $v" >&2; exit 2; fi
done
printf '%s  %s\n' \
  84784fbfa67d59e1f9e0bc51f5149411591b402099f0e630a591fc8e099cf535 "$repo/Computability/BusyBeaver/Research/PA/pa194-work/pa194-machine-ax-code/PA194MachineAXCode.lean" \
  458fb64b8b84629d36a6cc18a52a691757c84d240973463919e55eddceeff56e "$repo/Computability/BusyBeaver/Research/PA/pa194-work/pa194-machine-shift-mp-code/PA194MachineShiftMPCode.lean" \
  279bbab154e51f25144a5171b70708d0154457aac8fa3077712a31859166c8ee "$repo/Computability/BusyBeaver/Research/PA/pa194-work/pa194-scheduler-code/PA194SchedulerCode.lean" \
  dc7f58866f996ccd80bc3473fe26a5d9a43ad3099ddee4c7bc44eec96cb5cd23 "$repo/Computability/BusyBeaver/Research/PA/pa194-work/pa194-scheduler-halt/PA194SchedulerHalt.lean" \
  9e0227b4de22d5e048b448913367f13f146a08c71330e8ebd6b8d33616868f6b "$repo/Computability/BusyBeaver/Research/PA/pa194-work/pa194-scheduler-iteration/PA194SchedulerIteration.lean" \
  a6ff98751ef52efd5969f002536920e749917ded437806bddbf08f96719b69ca "$schedsrc/PA194SchedulerFetchFresh.lean" \
  bcdf965a454fa001035e87ae87d7ce0beb36a30a238ab5ef4f1062a394bdb758 "$schedsrc/PA194SourceFetchLoop.lean" \
  ff2086387bc3de5a2843bdb7b13ca72b1cd2e2c65866125b4de8610cb40c23f6 "$schedsrc/PA194SchedulerFetchPositive.lean" \
  24d3b73bb21939d35a06967703c761b9f0b8b5b2166efc1af0fd1caf837baee8 "$schedsrc/PA194SchedulerPackedFetchPositive.lean" \
  8bc5d4683534bfd1599d8bf9538b819d3ad9ecc64d817af35d72716f66655c67 "$schedbase/PA194MachineStack.olean" \
  f757ee5c4914a43d7630c83d38669f24df2f8b3aab8e5328ad2763728d586794 "$schedbase/PA194PathIterator.olean" \
  1721b3eddfa71be7fcc2ba27002fd1dda6acade9003ce89aaafaad3e14386c5d "$schedbase/PA194TargetProofLeaf.olean" \
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
task_dir=$(mktemp -d "${TMPDIR:-/dev/shm}/pa194-source-pc-bound.XXXXXXXX")
trap 'rm -rf "$task_dir"' EXIT
cd "$repo"
lake_path=$(lake env printenv LEAN_PATH)
view="$task_dir/overlay-view"
python3 - "$view" "$baseline" "$graph" "$schedbase" <<'PYTHON'
from pathlib import Path
import sys
out=Path(sys.argv[1]); roots=list(map(Path,sys.argv[2:])); chosen={}; conflicts=[]
for root in roots:
  for p in root.rglob('*'):
    if not p.is_file() or not ('.olean' in p.name or p.name.endswith('.ir')): continue
    rel=p.relative_to(root); dst=out/rel
    if rel in chosen:
      if p.name.endswith('.olean'): conflicts.append(str(rel))
      continue
    dst.parent.mkdir(parents=True,exist_ok=True); dst.symlink_to(p.resolve()); chosen[rel]=str(root)
print('Overlay-view objects:',len(chosen),'overlapping names:',len(conflicts))
print('Precedence: coherent controller baseline, code-graph overlay, prebuilt scheduler overlay')
print('Overlapping names are not assumed byte-identical or closure-compatible.')
PYTHON
export LEAN_PATH="$task_dir:$view:$project:$package:$lake_path"
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
for spec in pa194-machine-ax-code:PA194MachineAXCode pa194-machine-shift-mp-code:PA194MachineShiftMPCode pa194-scheduler-code:PA194SchedulerCode pa194-scheduler-halt:PA194SchedulerHalt pa194-scheduler-iteration:PA194SchedulerIteration; do
  d=${spec%%:*}; m=${spec#*:}
  cp "$repo/Computability/BusyBeaver/Research/PA/pa194-work/$d/$m.lean" "$task_dir/$m.lean"
  echo "Checking $m"
  lake env env LEAN_PATH="$LEAN_PATH" lean -j1 -R "$task_dir" -o "$task_dir/$m.olean" "$task_dir/$m.lean" 2>&1 | tee "$task_dir/$m.log"
  if rg -q 'sorryAx' "$task_dir/$m.log"; then echo 'Unexpected sorryAx' >&2; exit 1; fi
done
for m in PA194SchedulerFetchPositive PA194SchedulerPackedFetchPositive PA194SchedulerFetchFresh PA194SourceFetchLoop; do
  cp "$schedsrc/$m.lean" "$task_dir/$m.lean"
  echo "Checking $m"
  lake env env LEAN_PATH="$LEAN_PATH" lean -j1 -R "$task_dir" -o "$task_dir/$m.olean" "$task_dir/$m.lean" 2>&1 | tee "$task_dir/$m.log"
  if rg -q 'sorryAx' "$task_dir/$m.log"; then echo 'Unexpected sorryAx' >&2; exit 1; fi
done
for spec in PA194MachineAXCode:axCode_preserves PA194MachineShiftMPCode:shift_preserves PA194SchedulerCode:choose0_model PA194SchedulerHalt:halt_implies_provable PA194SchedulerIteration:step_fields PA194SchedulerFetchPositive:positiveFetchPrefix PA194SchedulerPackedFetchPositive:packedPositiveFetchPrefix PA194SchedulerFetchFresh:freshFetchPrefix PA194SourceFetchLoop:sourceInc PA194SourceFetchLoop:sourceJump PA194SourceFetchLoop:sourceDecPositive PA194SourceFetchLoop:drainLoop; do
  module=${spec%%:*}; thm=${spec#*:}
  rg -q "^'$module\.$thm' depends on axioms:" "$task_dir/$module.log"
done
echo 'PASS: scheduler/controller fetch prefixes and source drain loop body checked; overlapping prerequisite overlays remain prebuilt and not closure-audited.' 
