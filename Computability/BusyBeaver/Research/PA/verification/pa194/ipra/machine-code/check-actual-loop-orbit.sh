#!/usr/bin/env bash
set -euo pipefail
if (($# != 26)); then
  echo "usage: $0 REPO SOURCE_DIR CONTROLLER_SOURCE_DIR BRIDGE_SOURCE_DIR SITE27_BASELINE CODE_GRAPH_OVERLAY PROJECT_FOUNDATION PACKAGE_FOUNDATION SITE28_SOURCE SITE28_COMPLETE SITE28_FINISH SITE28_SEED SITE28_AFTER_CARRY SITE28_ROUND SITE28_CODES SITE29_INCREMENT SITE29_RETURN SITE29_IDENTITIES SITE29_COMPLETE DYNAMIC28_STAGE DYNAMIC29_STAGE ONE_SPARE_STAGE SITE30_JUMP DYNAMIC28_SOURCE DYNAMIC29_SOURCE ITERATION_SOURCE" >&2
  exit 2
fi
repo=$(realpath "$1")
source=$(realpath "$2")
controller=$(realpath "$3")
bridge=$(realpath "$4")
baseline=$(realpath "$5")
graph=$(realpath "$6")
project=$(realpath "$7")
package=$(realpath "$8")
site28src=$(realpath "$9")
complete=$(realpath "${10}")
finish=$(realpath "${11}")
seed=$(realpath "${12}")
aftercarry=$(realpath "${13}")
round=$(realpath "${14}")
codes=$(realpath "${15}")
inc29=$(realpath "${16}")
ret29=$(realpath "${17}")
ids29=$(realpath "${18}")
complete29=$(realpath "${19}")
dyn28=$(realpath "${20}")
dyn29=$(realpath "${21}")
onespare=$(realpath "${22}")
jump30=$(realpath "${23}")
dyn28src=$(realpath "${24}")
dyn29src=$(realpath "${25}")
iteration=$(realpath "${26}")
check_iteration_sources() {
 printf '%s  %s\n' \
  b0c4f50a0f5e8cdd915125fce3a5265de44e51846f182793b753c19dbf5f05ab "$iteration/PA194ModelLoopIteration.lean" \
  a700635165680c80d9ad6e7f83d59b2945122b8e39cc59d7f7fa130a4e603ad4 "$iteration/PA194ModelLoopState.lean" \
  faad42fb3d1b325f964b17bc7e4fbbcae295d7d0327ab00f7f983dff530cbd90 "$iteration/PA194ModelLoopFrame.lean" \
  7649b0e67e156142f1235c6b65cec29a5476a521fc8994c1122e7100f33db93f "$iteration/PA194ModelSourceLoop.lean" \
  7068b37b47fc4b70001b3fb8ce1ec44d011f7b56282e7d2f3176a8660d61613c "$iteration/PA194ModelLoopFour.lean" \
  1c87a66cea535481d17756dcd9051c91e67f1ed31b8570d6d7e7047c3d6ecee5 "$iteration/PA194ControllerLoopFrame.lean" \
  8faf78f1c7eb47de0b3e3dc6245f454d4b1272a93f7248f1c79c4ffcfc3883d9 "$iteration/PA194ActualSourceLoop.lean" \
  29c14ff45ea88dd71872f5a38f5bd843a3368842ce25464dafc95d9e9e2e5c92 "$iteration/PA194ActualSourceRun.lean" \
  946624c39b8aaa38eba01b8bb6fbd4ef8ab2c9bd7a478a36ab8d3c45e90d5af5 "$iteration/PA194ActualSourceExit.lean" \
  cb65d7b89d8ebd92a9548ab07815a3c45b0c1fc0833f9ca7323a7f8329ba7052 "$iteration/PA194ActualSourceRunSentence.lean" \
  1e679ce1c7e75509faf1a70a7032c9eba1d30e89c9659e3f73ea5db912772325 "$iteration/PA194ActualSourceExitSentence.lean" \
  9d79152ceb75b89a42812ddaf3b5be20c7b737d9ca4db434dc7f2f4a1c4a18dd "$iteration/PA194ActualLoopOrbit.lean" \
  | sha256sum -c -
}
check_iteration_sources
for v in GIT_DIR GIT_WORK_TREE GIT_INDEX_FILE GIT_OBJECT_DIRECTORY GIT_ALTERNATE_OBJECT_DIRECTORIES; do
  if [[ -v "$v" ]]; then echo "Refusing inherited $v" >&2; exit 2; fi
done
printf '%s  %s\n' \
  df6e26ea4e7b5a2ad132b1ef71fb00cfd6875b65e8dab346907c0487684482f8 "$site28src/PA194Site27PositiveThen28.lean" \
  26a8b55076a20137b84a98318f34ef3c5ffe4d143c8c30f541ce2d1fcff67078 "$site28src/PA194Site25Then27Then28.lean" \
  c6a7b8d5f765ef728a40419df492837e35fa512f1a261817ce9f93e19e21dc38 "$site28src/PA194SeedControllerReach29.lean" \
  3d1548d7194efbbf40dd7184176568fb1a2448510a26aba88a3f438d6ae9be11 "$baseline/PA194Path27Frame.olean" \
  c8fb1b002430120e1f44c91b8107fadfada6eda908b4729dbdfb3208c37edc11 "$site28src/PA194SourceSite29Controller.lean" \
  3c7229cab856463a8737239c1cf850b940d1f187ea7d62f318d414716a6004e0 "$site28src/PA194SourceSite29Physical.lean" \
  598753a5d321ff88aea59500020f22ab56989fdf1cf08c71b3c175787946dc84 "$site28src/PA194SeedControllerReach30.lean" \
  1028b03158b129a0d8956fc9c6fb60e660d66f1608c49c54b7e05aa93f1cc88f "$inc29/PA194Site29ToIncrement.olean" \
  a3805c21b42ec3b5f04cb5149171db4c81b850bf4ead136579d0f3ec944162f3 "$ret29/PA194Site29ReturnToRoot.olean" \
  87b74b07943182b3e95be6e9a861fc79bcb34a0b8a606d57f7824a0772ad11f6 "$ids29/PA194Site29ReturnPath30.olean" \
  d966ae2a163c61bca4606454ad425725a3a84403050a301dfbe1e24e692e3f36 "$ids29/PA194Site29OutputWithCarry.olean" \
  f0ef640404e62d8d7ff0f037add09ef697cf895e8a5cf36f9c7f4292e48ff344 "$complete29/PA194Site29Complete.olean" \
  b37d7882568a686a6e9ea4e315c5075c4596a70f740e27f1a3450fff37855ca1 "$site28src/PA194SourceSite28Physical.lean" \
  bf17a5e3b0c3ed468329b4bb585b9a170993556421a71eae9cde5b3612c02dbb "$complete/PA194Site28Complete.olean" \
  d27dff3bc7b3ec0b787960729c19c036d70a816dcbf6a50c640f72d8115afbb1 "$complete/PA194Site28OutputFile.olean" \
  ad9dda641b3c8fe1ef1280d22e436c8b321bddeeae2f55900f4f7a72cb4ea35e "$seed/PA194Site28SeedRoundTrip.olean" \
  bf5e329caca4f8633c5b899fb2ef672ffc07728d249fd55277ae999ec4ad0fa6 "$baseline/PA194StartupSourceFrame.olean" \
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
  d0eafa9cc090cfbff9d7ccad06cdd1bde91f92f5c2cf05784d5df08b90ec9c2d "$bridge/PA194Site25FrameRelation.lean" \
  bb59f1fbaf7d97e8512ecf3e4efc71c28e1b210d421817b4e218109cf964891c "$bridge/PA194SourceSite27Physical.lean" \
  59f11e119badc7eb8ed920df7c87e4eb4631f9a2732e3e15cca177fd7941f416 "$bridge/site27-baseline-receipt.json" \
  72b392c77ea0bc7cc4bf0012fd9aa161ca79458c4e8558363708dd4de679b388 "$repo/Computability/BusyBeaver/Research/PA/verification/pa194/ipra/machine-code/PA194Path27To28.lean" \
  d569cc4723e2c87b80534f9aadf810d22df5fb70afc1aec615e4e245a95e7cbf "$bridge/physical-baseline-receipt.json" \
  6d34ca8f62b040c0c1c4b0a83c10370aaf28edb029e5e998274e187032e0b543 "$baseline/site27-coherent-manifest.json" \
  4da56e9178bdb0950df59671d505fde659bb2f709aaecf0a108231bdfa18ba6a "$repo/Computability/BusyBeaver/Research/PA/verification/pa194/ipra/machine-code/PA194Site27PathStep.lean" \
  69044b06d8b83ad8562a76af549df11391d936ebfb87b9f0b1ba2963b7301ed0 "$repo/Computability/BusyBeaver/Research/PA/verification/pa194/ipra/machine-code/PA194Path25To27.lean" \
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
  bdfeb2a5aa83198a61c345ccb137a8bf99ef9fc23bccc7f6fc96a1d3295eb094 "$repo/Computability/BusyBeaver/Research/PA/verification/other-machines/pa195-work/pa195-calibration/PA194CodeGraph.lean" | sha256sum -c -
printf '%s  %s\n' \
 abec7dfd02e44ab7effaed3666cfc635a6b96d3ba8c9469b4afd238e29b52c45 "$dyn28src/PA194SourceSite28DynamicPhysical.lean" \
 a55dd65327201c92de8d743b8f73582c0fc6c9c16b720ea0d745b2911c0461ed "$dyn29src/PA194SourceSite29DynamicController.lean" \
 43ec75d82744e7a882473ff692b9b43e2631b0a0e922b699012a233044cf8c1b "$dyn29src/PA194SourceSite29DynamicPhysical.lean" \
 1127cd8a2210b88c27b446ab2c7c80ee87a71a4ae2ac85c06a1e315253e1b497 "$dyn29src/PA194SourceSite28Then29Dynamic.lean" \
 7dbe58403af330ce49ae9eeca42587b2b12b67d5fe5e9e927a02f221c07cc114 "$dyn29src/PA194SourceDynamicLoop.lean" \
 40637c6f14571e8530ce8a348da93df5ff5d2037ac7c16b47b65be650d3550a6 "$site28src/PA194SourceSite30Physical.lean" | sha256sum -c -
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
python3 - "$bridge/site27-baseline-receipt.json" "$baseline" <<'PYTHON'
import hashlib,json,sys
from pathlib import Path
receipt=json.loads(Path(sys.argv[1]).read_text()); root=Path(sys.argv[2])
for name,expected in receipt.items():
    path=root/(name+'.olean')
    if hashlib.sha256(path.read_bytes()).hexdigest() != expected: raise SystemExit(f'baseline object mismatch: {path}')
print('Site-27 physical baseline direct objects:',len(receipt),'OK')
PYTHON
python3 - "$baseline" "$complete" "$finish" "$seed" "$aftercarry" "$round" "$codes" "$inc29" "$ret29" "$ids29" "$complete29" "$dyn28" "$dyn29" "$onespare" "$jump30" <<'PYTHON'
from pathlib import Path
import hashlib,sys
seen={}; overlaps=0
for root in map(Path,sys.argv[1:]):
  for p in root.glob('*.olean'):
    if p.is_symlink(): raise SystemExit(f'symlinked machine object {p}')
    if p.name in seen:
      old=seen[p.name]
      if hashlib.sha256(old.read_bytes()).digest()!=hashlib.sha256(p.read_bytes()).digest():
        raise SystemExit(f'different overlapping machine object {p}: {old}')
      overlaps+=1
    else: seen[p.name]=p
print('Machine roots:',len(seen),'objects;',overlaps,'overlaps checked byte-identical')
PYTHON
task_dir=$(mktemp -d "${TMPDIR:-/dev/shm}/pa194-site27-controller-physical.XXXXXXXX")
trap 'rm -rf "$task_dir"' EXIT
cd "$repo"
lake_path=$(lake env printenv LEAN_PATH)
export LEAN_PATH="$task_dir:$dyn28:$dyn29:$onespare:$jump30:$complete29:$ids29:$ret29:$inc29:$complete:$finish:$seed:$aftercarry:$round:$codes:$baseline:$graph:$project:$package:$lake_path"
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
for m in PA194Site27PathStep PA194Path25To27 PA194SourceSite25Physical PA194SourceSite25Positive PA194Site25FrameRelation PA194Path27To28 PA194SourceSite27Physical; do
  case "$m" in
    PA194Site27PathStep|PA194Path25To27|PA194Path27To28) cp "$repo/Computability/BusyBeaver/Research/PA/verification/pa194/ipra/machine-code/$m.lean" "$task_dir/$m.lean" ;;
    *) cp "$bridge/$m.lean" "$task_dir/$m.lean" ;;
  esac
  echo "Checking $m"
  lake env env LEAN_PATH="$LEAN_PATH" lean -j1 -R "$task_dir" -o "$task_dir/$m.olean" "$task_dir/$m.lean" 2>&1 | tee "$task_dir/$m.log"
  if rg -q 'sorryAx' "$task_dir/$m.log"; then echo 'Unexpected sorryAx' >&2; exit 1; fi
done
rg -q "^'PA194SourceSite25Physical.zeroBranch' depends on axioms:" "$task_dir/PA194SourceSite25Physical.log"
rg -q "^'PA194SourceSite25Positive.positiveBranch' depends on axioms:" "$task_dir/PA194SourceSite25Positive.log"
rg -q "^'PA194SourceSite25Positive.updateRegister8' depends on axioms:" "$task_dir/PA194SourceSite25Positive.log"
rg -q "^'PA194Site25FrameRelation.site25Step' depends on axioms:" "$task_dir/PA194Site25FrameRelation.log"
for thm in site27Instruction updateRegister0 positiveBranch matchedPositiveStep; do
  rg -q "^'PA194SourceSite27Physical.$thm' depends on axioms:" "$task_dir/PA194SourceSite27Physical.log"
done
cp "$site28src/PA194SourceSite28Physical.lean" "$task_dir/PA194SourceSite28Physical.lean"
echo 'Checking PA194SourceSite28Physical'
lake env env LEAN_PATH="$LEAN_PATH" lean -j1 -R "$task_dir" -o "$task_dir/PA194SourceSite28Physical.olean" "$task_dir/PA194SourceSite28Physical.lean" 2>&1 | tee "$task_dir/PA194SourceSite28Physical.log"
if rg -q 'sorryAx' "$task_dir/PA194SourceSite28Physical.log"; then echo 'Unexpected sorryAx' >&2; exit 1; fi
for thm in site28Instruction updatedRegs controllerStep sourcePhysicalNested physicalClock sourcePhysical matchedStep; do
  rg -q "^'PA194SourceSite28Physical.$thm' depends on axioms:" "$task_dir/PA194SourceSite28Physical.log"
done
cp "$site28src/PA194Site27PositiveThen28.lean" "$task_dir/PA194Site27PositiveThen28.lean"
echo 'Checking PA194Site27PositiveThen28'
lake env env LEAN_PATH="$LEAN_PATH" lean -j1 -R "$task_dir" -o "$task_dir/PA194Site27PositiveThen28.olean" "$task_dir/PA194Site27PositiveThen28.lean" 2>&1 | tee "$task_dir/PA194Site27PositiveThen28.log"
if rg -q 'sorryAx' "$task_dir/PA194Site27PositiveThen28.log"; then echo 'Unexpected sorryAx' >&2; exit 1; fi
rg -q "^'PA194Site27PositiveThen28.positiveThenIncrement' depends on axioms:" "$task_dir/PA194Site27PositiveThen28.log"
for m in PA194Site25Then27Then28 PA194SeedControllerReach29; do
  cp "$site28src/$m.lean" "$task_dir/$m.lean"
  echo "Checking $m"
  lake env env LEAN_PATH="$LEAN_PATH" lean -j1 -R "$task_dir" -o "$task_dir/$m.olean" "$task_dir/$m.lean" 2>&1 | tee "$task_dir/$m.log"
  if rg -q 'sorryAx' "$task_dir/$m.log"; then echo 'Unexpected sorryAx' >&2; exit 1; fi
done
rg -q "^'PA194Site25Then27Then28.zeroPositiveIncrement' depends on axioms:" "$task_dir/PA194Site25Then27Then28.log"
rg -q "^'PA194SeedControllerReach29.blankAndThreeSteps' depends on axioms:" "$task_dir/PA194SeedControllerReach29.log"
for m in PA194SourceSite29Controller PA194SourceSite29Physical PA194SeedControllerReach30; do
  cp "$site28src/$m.lean" "$task_dir/$m.lean"
  echo "Checking $m"
  lake env env LEAN_PATH="$LEAN_PATH" lean -j1 -R "$task_dir" -o "$task_dir/$m.olean" "$task_dir/$m.lean" 2>&1 | tee "$task_dir/$m.log"
  if rg -q 'sorryAx' "$task_dir/$m.log"; then echo 'Unexpected sorryAx' >&2; exit 1; fi
done
for spec in PA194SourceSite29Controller:site29Instruction PA194SourceSite29Controller:updateRegister6 PA194SourceSite29Controller:updatedRegs PA194SourceSite29Controller:controllerStep PA194SourceSite29Physical:sourcePhysical PA194SeedControllerReach30:blankAndFourSteps; do
  module=${spec%%:*}; thm=${spec#*:}
  rg -q "^'$module\.$thm' depends on axioms:" "$task_dir/$module.log"
done
echo 'PASS: blank to physical site 30 and four actual encoded-controller steps agree; staged machine and foundational overlays remain prebuilt.'       

for m in PA194SourceSite28DynamicPhysical PA194SourceSite29DynamicController PA194SourceSite29DynamicPhysical PA194SourceSite28Then29Dynamic PA194SourceSite30Physical PA194SourceDynamicLoop; do
  case "$m" in
    PA194SourceSite28DynamicPhysical) cp "$dyn28src/$m.lean" "$task_dir/$m.lean" ;;
    PA194SourceSite30Physical) cp "$site28src/$m.lean" "$task_dir/$m.lean" ;;
    *) cp "$dyn29src/$m.lean" "$task_dir/$m.lean" ;;
  esac
  echo "Checking $m"
  lake env env LEAN_PATH="$LEAN_PATH" lean -j1 -R "$task_dir" -o "$task_dir/$m.olean" "$task_dir/$m.lean" 2>&1 | tee "$task_dir/$m.log"
  if rg -q 'sorryAx' "$task_dir/$m.log"; then echo 'Unexpected sorryAx' >&2; exit 1; fi
done
for spec in PA194SourceSite28DynamicPhysical:sourcePhysical PA194SourceSite29DynamicController:controllerStep PA194SourceSite29DynamicPhysical:sourcePhysical PA194SourceSite28Then29Dynamic:twoSteps PA194SourceSite30Physical:sourcePhysical PA194SourceDynamicLoop:fourSteps; do
 module=${spec%%:*}; thm=${spec#*:}
 rg -q "^'$module.$thm' depends on axioms:" "$task_dir/$module.log"
done
echo 'PASS: dynamic 27→28→29→30→27 controller and physical loop; staged machine roots and foundational overlays remain prebuilt.'

for m in PA194ModelLoopIteration PA194ModelLoopState PA194ModelLoopFrame PA194ModelSourceLoop PA194ModelLoopFour PA194ControllerLoopFrame PA194ActualSourceLoop PA194ActualSourceRun PA194ActualSourceExit PA194ActualSourceRunSentence PA194ActualSourceExitSentence PA194ActualLoopOrbit; do
  cp "$iteration/$m.lean" "$task_dir/$m.lean"
  echo "Checking $m"
  lake env env LEAN_PATH="$LEAN_PATH" lean -M6000 -j1 -R "$task_dir" -o "$task_dir/$m.olean" "$task_dir/$m.lean" 2>&1 | tee "$task_dir/$m.log"
  if rg -q 'sorryAx' "$task_dir/$m.log"; then echo 'Unexpected sorryAx' >&2; exit 1; fi
done
for spec in PA194ModelLoopIteration:modelIteration PA194ModelLoopState:iterPacked PA194ModelLoopFrame:modelFrame PA194ModelSourceLoop:sourceIteration PA194ModelLoopFour:groupFour PA194ControllerLoopFrame:frameSource PA194ActualSourceLoop:oneLoop PA194ActualSourceLoop:sourceIteration PA194ActualSourceRun:sourceRunIteration PA194ActualSourceRun:reachesZero PA194ActualSourceExit:zeroStep PA194ActualSourceExit:exitsAt31 PA194ActualSourceRunSentence:modelSentence PA194ActualSourceRunSentence:classicalPRA PA194ActualSourceRunSentence:nativeIPRA PA194ActualSourceExitSentence:modelSentence PA194ActualSourceExitSentence:classicalPRA PA194ActualSourceExitSentence:nativeIPRA PA194ActualLoopOrbit:controllerSource PA194ActualLoopOrbit:frameOrbit; do
 module=${spec%%:*}; thm=${spec#*:}
 rg -q "^'$module\.$thm' depends on axioms:" "$task_dir/$module.log"
done
check_iteration_sources
echo 'PASS: actual PA194 source run, exit, native iPRA sentences and coded physical frame orbit; staged machine/foundation roots remain prebuilt.'
