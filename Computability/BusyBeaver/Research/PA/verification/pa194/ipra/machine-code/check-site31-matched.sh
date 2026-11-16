#!/usr/bin/env bash
set -euo pipefail
if (($# != 9)); then echo "usage: $0 REPO SITE27_BASELINE PROJECT_FOUNDATION PACKAGE_FOUNDATION SOURCE TAIL_STAGE CARRY_STAGE FETCH_SOURCE_MANIFEST_ROOT NEW_OUTPUT" >&2; exit 2; fi
repo=$(realpath "$1")
baseline=$(realpath "$2")
project=$(realpath "$3")
package=$(realpath "$4")
source=$(realpath "$5")
tail=$(realpath "$6")
carry=$(realpath "$7")
fetch=$(realpath "$8")
out=$(realpath -m "$9")
if [[ -e "$out" || -L "$out" ]]; then echo "Refusing existing output: $out" >&2; exit 2; fi
for v in GIT_DIR GIT_WORK_TREE GIT_INDEX_FILE GIT_OBJECT_DIRECTORY GIT_ALTERNATE_OBJECT_DIRECTORIES; do
  if [[ -v "$v" ]]; then echo "Refusing inherited $v" >&2; exit 2; fi
done
check_inputs() {
 printf '%s  %s\n' \
  6d34ca8f62b040c0c1c4b0a83c10370aaf28edb029e5e998274e187032e0b543 "$baseline/site27-coherent-manifest.json" \
  58493be34ff68b69f7cdb9cafa7eadffac307262f1c62824c55867719b5a07bf "$baseline/PA194Site27HeaderDispatch.olean" \
  cf9150dbbb719a01bff0c7193ede46e8e57a9ae2ea8e80317f4855416ab0cc15 "$baseline/PA194LeftRows.olean" \
  c4aef4576f072a828247a9d934260cce89302bf31bcfc0aa2d2f48963f4cbcd2 "$baseline/PA194Path27Header.olean" \
  95d26c326cac59eb185413d7f3c0da2f85e5de983d663e525f76160c9d200327 "$repo/Computability/BusyBeaver/Research/PA/verification/pa194/ipra/machine-code/PA194Path31Header.lean" \
  318640b93f57c641cc76baca6e0738519e17135a9557d3b5e705773eb4fde328 "$source/PA194Site31HeaderDispatch.lean" \
  1b35891a7f5f994f0f69f829653fb5204ae28423fbf9ed23f2c244ee28748948 "$source/PA194Site31HeaderTo49.lean" \
  7f6498a27a4fc0f9809d64eb4695f23b4ca275eda065503e458412e7a7637cdd "$baseline/PA194EightyFourTo17.olean" \
  70cb1e6fba93d0c8beaa2ffb1591fb22a7e199e89d411777e6293f33a88ac1a7 "$baseline/PA194HeaderController.olean" \
  4b76994df8087b5967fc44030267c8ffa6ce4a111dadb2d07c0ae1d454eba403 "$baseline/PA194RegisterPermutation.olean" \
  e4bb76cd312ffdf6ef6a1d016baf8265197087ba5afc24fb2d84c165dc3e61f8 "$source/PA194Site31HeaderTo84.lean" \
  02bf1c3783612cd3e0faf228d7c9e992b86ce1a8af7fd06b028daf49b0017d83 "$source/PA194Site31HeaderTo17.lean" \
  d32e0974c9cbada03686bcd5b0b138c7aec2debe4491cfee12f966f201fbfefd "$baseline/PA194ZeroReturnFrom16.olean" \
  dc3a99072faa1338c896278f3a667a00814d33ee882c42b3b4ac526bf361f145 "$baseline/PA194LeftOneWriteOne.olean" \
  681bf6ac6786b56c6765bd8e97b62ea36e1dca2634d9c13257da557ad203beaa "$source/PA194Site31HeaderReturn.lean" \
  746a276c9e5771487dc0e33eeb903af735c6deb98d67b639232d3ff26f63fa7f "$source/PA194Site31HeaderPass.lean" \
  e95cb853a52008a3e8e97a0468ff193c0465a80af38e8c77d98013f08b4f90bd "$baseline/PA194Site27Scan106.olean" \
  c92ba7ee348a216801074b6011adad2d472c4c3cc8b881a947313a5db5c0a0f8 "$source/PA194Site31HeaderPassPath.lean" \
  66059e3930ba8832dae9a3009ec1fe8a39715a6a008dbe10fb4ec72124320d2f "$source/PA194Site31MarkedTo106.lean" \
  afdaf4bc28d32990f9c951fa2c0cd22b947bb7b4b8db6f22c1228511899d2aff "$source/PA194Site31To71.lean" \
  1832677648c49268311d2e57e1677d6743d6de88f969a182853c9e85ec829431 "$baseline/PA194Site27ScanRewind.olean" \
  0532924ec521b5039dc25e3687065538248b440eff23aa16f24c6eb3c0e063d5 "$baseline/PA194SixteenScanInvariant.olean" \
  6060f560b9c62f4e3b80db1158faf0d06dee719bb1d1820318e7a1e08d9c2c7b "$baseline/PA194SixteenExitComposition.olean" \
  d858245985997ab4c9ed161ecedb69e8f569de0f3cb6ab816c0e368ec568f82b "$source/PA194Site31SecondTo17.lean" \
  be245937dcd1eec91adb3155ddcd90032a6c4fad8a56b3995ccabdc82b3b00f6 "$source/PA194Site31SecondReturn.lean" \
  ab544a0610d183add902a68ec45fc21d2efcee9f96734ce892f7f37b669c2baf "$source/PA194Site31SecondUnmark.lean" \
  f538e0a9cdd6003814b9d819dcdffebbe065bf670e4c4c4274d12bd60f5dc025 "$source/PA194Site31SecondRoot.lean" \
  94f2b26a82187d92edbc8fb69a9ec009873fea847d8d01f2e4798addc8920824 "$source/PA194Site31RootTo2.lean" \
  c8108ea94c97822c2d0d8a5af0b7e640318bec0d52914524941e093aa8aeac98 "$source/PA194Site31To2.lean" \
  8cfef270e036b8ea92a3bea46e274896e7e7d48edd96b10f3617ffe8f8f10ec7 "$source/PA194Site31SelectedThrough.lean" \
  bcafed39cb6dd9bed126efaa27c13ae2f90f124d356ea74cbf0c431bed1f7340 "$source/PA194Site31Selected.lean" \
  a51cac85865adfda0306648e1e3bb20843bc36db6fe541c70494340bd679b746 "$source/PA194Site31ToSelected.lean" \
  3b5ab4d23ed072bf5ffdce4f973790fa8e701181d69952023fcea9414165170b "$source/PA194Site31DynamicTail.lean" \
  117bab8280510352156a0fb1f1b7c4277cf77f6e9f2e08bdacd8387e8d7a108a "$source/PA194Site31DynamicIncrement.lean" \
  c09210dcb82c3eb4695847a3bebed65c952e7e80aeca902a3f703dc70d7b5b0f "$source/PA194Site31IncrementSelected.lean" \
  8ef045dd90bdfd26ea6da2d629db4a6336f0db0cba0b87eec5cc88703346580c "$source/PA194Site31ReturnPrefix.lean" \
  086253e38f9793cec6513af7e533fa1d01f080dfe1f4996acd7f85869fbe4cad "$source/PA194Site31IncrementReturn.lean" \
  6acbd85a4da5a70803821f93ecb780c3a7c85959b40fa5261a1ffdfbeb381f23 "$repo/Computability/BusyBeaver/Research/PA/verification/pa194/ipra/machine-code/PA194IncrementFront.lean" \
  9565d5637e3159da55a0a8f847f1c48771d040b2e6c87a689cb917244e5ff74b "$repo/Computability/BusyBeaver/Research/PA/verification/pa194/ipra/machine-code/PA194Site28IncrementWrite.lean" \
  648916151fda54f935977836db659d73a77617dbb70738b8a7664b964b9a13e4 "$baseline/PA194PrefixFile.olean" \
  561ee9cbfa02ff5a9acbd17e967a15d001a71790368cafdc3cddc6681c9c9a53 "$baseline/PA194MarkedFile.olean" \
  0d7c7c493aaec2893a57794aa4047bad6097e15f029755e93c88653e337261e6 "$baseline/PA194GenericRightScan.olean" \
  6c5605b5a35486f162b39e12697665895d9bfed51005c44c288e7ec0aaaa1f02 "$baseline/PA194RightRows.olean" \
  f61c2acfecdeec888548b52fc7b67d0c1e09038ee7f3fe619874d9ef73dd58e4 "$baseline/PA194OnesCommute.olean" \
  3a56b41ea7dbabb6418d2aba83f773154fa160b39613c83f7b5e32d245e0b34c "$baseline/PA194ReturnFile.olean" \
  9fed8a25881629b19559d093f881217d37c4c6dbd8be9614eb1117aaba313a28 "$baseline/PA194PrefixReturn.olean" \
  b13712e5ce92964b218b97297c1fbe0775e57ba367fe5dbfdae38c6e59d24617 "$tail/PA194OneSpareRoundTrip.olean" \
  62c58fdbd82a2e83b69e354779d430f3f5ab9204c588cc1f0ef2f071cb853afd "$tail/PA194OneSpareIdentities.olean" \
  b209cd050545f75a761c95e2cfa08aac734181af8e85426359c15bffd95ec777 "$tail/PA194OneSpareIterate.olean" \
  7aa26bb42eb112807a47dc1b22feb5e14404e221981a6dc14d4f6e681a94b0bf "$tail/PA194OneSpareReturn.olean" \
  3b9735f9c08d9aaefcdb2ea6388911c89c9ae9452c64ae51c925fc58d9958eb8 "$carry/PA194Site28BlankExit.olean" \
  ef0684e7ed74adee488d5b3ec8734c38e9536d8651a64e4032a860f479fc32f8 "$carry/PA194LeftZeroWriteOne.olean" \
  40341fb6c6777dd939d9c5e1334015e5189af147c80b1cb2de9e8f5d42759d05 "$source/PA194Path32Header.lean" \
  af00604cd8e5f37d6cc588c3a0439e88b01570c1132640daa5b97277b7a7ede3 "$source/PA194Site31ReturnHeader.lean" \
  1cc2b282441cb3d7cda7fe1e429880a07df5d97be7d8be12fd09565968f55d49 "$source/PA194Site31AfterSelectedTo32.lean" \
  7f27d7337033bd98fa8447e97735d7610a30d7e2e6054f563a27e82792c2c5aa "$source/PA194Site31AfterRun.lean" \
  1ca3207a3be80751d2038a36926339ee081c6757831332faf6c0ee094eb6fac2 "$source/PA194Site31RootTo32.lean" \
  6b596e80c021c6a833d8d5ff66bcb57dcf5ff5b3eeea2ce142b9e082011b2c57 "$repo/Computability/BusyBeaver/Research/PA/verification/pa194/ipra/machine-code/PA194Site28ReturnHeader.lean" \
  8f193d3a288975b36452be71a4d4ab82b01688320b2ae2d8697fa745e9f13409 "$repo/Computability/BusyBeaver/Research/PA/verification/pa194/ipra/machine-code/PA194Site29ReturnHeader.lean" \
  481e02652a55b760291e1828d90242bd9ab71e54d3a6c7cda898cbcd4b728a1b "$baseline/PA194Site27PositiveHeaderTo12.olean" \
  ebbbb95cb02b5aa648223f38be447a756b2f865cb0634ffa1fb72d3dc768a1a9 "$baseline/PA194ThirteenExitComposition.olean" \
  7febeb80efc04b37d85e5e178791324d94eecb0b44ceecbb48b8260080c105e2 "$baseline/PA194FirstThreeBlankTailTo16.olean" \
  4eecb3ebd6021a255fe75e23205033c6c8e67c7a1ecece6cdb509e37f0b56809 "$baseline/PA194Site27PositiveReturnFrom16.olean" \
  d64819b7e0ae2c52239b7ee81b0c489c91d85de8a2c129c1028b3e15ad6c015e "$source/PA194Site31UpdateVector.lean" \
  3f0f71462cf05bdbb5fe2018d766e104b7a982fd0dd47faca40f9c4142f147fc "$source/PA194Site31ReplaceSimple.lean" \
  965e49c61567bcc4304e7bd86efadb9ffc6b00c0181602c141f6af2096f8d5a4 "$source/PA194Site31FileSplit.lean" \
  c8f6e835e4ccf03e6ad29f39c7120d71e1819fa15ac5bef19daee47a24ae8a60 "$source/PA194Site31FileCombine.lean" \
  86e824b632c16d01988265d6067912b839b068e37740ccced2662c374841f569 "$source/PA194Site31OutputFile.lean" \
  250b060a416a0c62a4b011c5c5fe22d9586b80244968004e98dbb04c6d63a46f "$source/PA194Site31RootStep.lean" \
  70105c2463768da42439b8365e1798209d16d814d11d125c1c6cbeac8f48327a "$tail/PA194OneSpareFileRoundTrip.olean" \
  763a7fe17531d58211696a7f9f06034e8877f29ebdf0bd05c3e30ca8aaa22ed6 "$source/PA194SourceSite31Controller.lean" \
  0b0be9140bd79547d2284409a51256cc777330a3417afd47f92e5f533363be00 "$source/PA194SourceSite31Physical.lean" \
  34cc6d4bcc21aed6d9876985ad605a1efabd9d5919ae6636f8fb5512d5fdb66a "$source/build-site31-controller-closure.py" \
  22970fddb4704c19b7a1a2c76375cf2126f53b3cd362f5248ed0fd45ef941a02 "$fetch/source-closure.json" \
  f2bd14dd0d5f1238b6bcc2be9bd998c4077f4e844584d1b977ece4e94d8094ec "$baseline/ConfigurationStep.olean" \
  cecc8f2a6c1f45b717c9f0c822ba3fa376db2b2a2d79c296f320eefb9e494f7f "$baseline/PA194FiniteControls.olean" \
  064e4dacfa11962fdb8f2048b84511551747c804ca14daffaa7c640a24d197d3 "$baseline/PA194SourceProgram.olean" \
  06bf36b979a3a8d785b0939d4bb27a1c44c5742e4c0284a474ef781ac7bdb1a2 "$baseline/PA194StateOne.olean" \
  8b23b791247e4fb374ee0115773c59db0bd4eede5c3a14a4728758e3b6070778 "$baseline/PA194StepperCompose.olean" \
  5861390d138991912d3e1c74bac804b39068bb2f3481a896d4d63bf10d576c2a "$baseline/PackedDecoderModel.olean" \
  | sha256sum -c -
}
check_inputs
task_dir="$out"
mkdir -p "$task_dir"
cd "$repo"
lake_path=$(lake env printenv LEAN_PATH)
python3 - "$baseline" "$tail" "$carry" <<'PYCHECK'
import hashlib, pathlib, sys
seen={}
for root in map(pathlib.Path, sys.argv[1:]):
    for p in root.glob('*.olean'):
        if p.name in seen:
            other=seen[p.name]
            if hashlib.sha256(p.read_bytes()).digest() != hashlib.sha256(other.read_bytes()).digest():
                raise SystemExit(f'Conflicting machine objects: {p} and {other}')
        else:
            seen[p.name]=p
PYCHECK
export LEAN_PATH="$task_dir:$tail:$carry:$baseline:$fetch/foundation-view:$project:$package:$lake_path"
for m in PA194Path31Header PA194Site31HeaderDispatch PA194Site31HeaderTo49 PA194Site31HeaderTo84 PA194Site31HeaderTo17 PA194Site31HeaderReturn PA194Site31HeaderPass PA194Site31HeaderPassPath PA194Site31MarkedTo106 PA194Site31To71 PA194Site31SecondTo17 PA194Site31SecondReturn PA194Site31SecondUnmark PA194Site31SecondRoot PA194Site31RootTo2 PA194Site31To2 PA194IncrementFront PA194Site31SelectedThrough PA194Site31Selected PA194Site31ToSelected PA194Site28IncrementWrite PA194Site31DynamicTail PA194Site31DynamicIncrement PA194Site31IncrementSelected PA194Site31ReturnPrefix PA194Site31IncrementReturn PA194Path32Header PA194Site28ReturnHeader PA194Site29ReturnHeader PA194Site31ReturnHeader PA194Site31AfterSelectedTo32 PA194Site31AfterRun PA194Site31RootTo32 PA194Site31UpdateVector PA194Site31ReplaceSimple PA194Site31FileSplit PA194Site31FileCombine PA194Site31OutputFile PA194Site31RootStep; do
 case "$m" in
  PA194Path31Header|PA194IncrementFront|PA194Site28IncrementWrite|PA194Site28ReturnHeader|PA194Site29ReturnHeader) cp "$repo/Computability/BusyBeaver/Research/PA/verification/pa194/ipra/machine-code/$m.lean" "$task_dir/$m.lean" ;;
  *) cp "$source/$m.lean" "$task_dir/$m.lean" ;;
 esac
 echo "Checking $m"
 lake env env LEAN_PATH="$LEAN_PATH" lean -M6000 -j1 -R "$task_dir" -o "$task_dir/$m.olean" "$task_dir/$m.lean" 2>&1 | tee "$task_dir/$m.log"
 if rg -q 'sorryAx' "$task_dir/$m.log"; then echo 'Unexpected sorryAx' >&2; exit 1; fi
done
echo 'Rebuilding controller dependencies against the physical source-program baseline'
python3 "$source/build-site31-controller-closure.py" "$repo" "$fetch/source-closure.json" "$task_dir" "$baseline"
for m in PA194SourceSite31Controller PA194SourceSite31Physical; do
 cp "$source/$m.lean" "$task_dir/$m.lean"
 echo "Checking $m"
 lake env env LEAN_PATH="$LEAN_PATH" lean -M6000 -j1 -R "$task_dir" -o "$task_dir/$m.olean" "$task_dir/$m.lean" 2>&1 | tee "$task_dir/$m.log"
 if rg -q 'sorryAx' "$task_dir/$m.log"; then echo 'Unexpected sorryAx' >&2; exit 1; fi
done
for spec in PA194SourceSite31Controller:site31Instruction PA194SourceSite31Controller:updateRegister0 PA194SourceSite31Controller:updatedRegs PA194SourceSite31Controller:controllerStep PA194SourceSite31Physical:sourcePhysical; do
 module=${spec%%:*}; thm=${spec#*:}
 rg -q "^'$module\.$thm' depends on axioms:" "$task_dir/$module.log"
done
for spec in PA194Path31Header:path31 PA194Site31HeaderDispatch:row63one PA194Site31HeaderDispatch:row89zero PA194Site31HeaderDispatch:sevenSteps PA194Site31HeaderTo49:row46odd PA194Site31HeaderTo49:row65one PA194Site31HeaderTo49:path31Input PA194Site31HeaderTo49:to49 PA194Site31HeaderTo84:fiveSteps PA194Site31HeaderTo84:to84 PA194Site31HeaderTo17:site31HeaderTo17 PA194Site31HeaderReturn:returnTo24 PA194Site31HeaderPass:site31HeaderPass PA194Site31HeaderPassPath:firstPass PA194Site31MarkedTo106:markedTo106 PA194Site31To71:site31To71 PA194Site31SecondTo17:site31SecondTo17 PA194Site31SecondReturn:return17To24 PA194Site31SecondUnmark:unmarkTo24 PA194Site31SecondRoot:site31SecondRoot PA194Site31RootTo2:rootTo2 PA194Site31To2:site31To2 PA194IncrementFront:modelSelectedAndCarry PA194Site31SelectedThrough:selectedThrough PA194Site31Selected:selected PA194Site31ToSelected:site31ToSelected PA194Site28IncrementWrite:incrementWrite PA194Site31DynamicTail:tailRoundTrip PA194Site31DynamicIncrement:increment PA194Site31IncrementSelected:incrementSelected PA194Site31ReturnPrefix:returnPrefix PA194Site31IncrementReturn:incrementReturn PA194Path32Header:path32 PA194Path32Header:path32Word PA194Site28ReturnHeader:headerTo24 PA194Site29ReturnHeader:headerTo24 PA194Site31ReturnHeader:headerTo24 PA194Site31AfterSelectedTo32:afterSelectedTo32 PA194Site31RootTo32:rootTo32 PA194Site31UpdateVector:updateVector PA194Site31ReplaceSimple:replaceSix PA194Site31ReplaceSimple:replaceThree PA194Site31ReplaceSimple:vectorTail PA194Site31FileSplit:split PA194Site31FileCombine:combine PA194Site31OutputFile:outputFile PA194Site31RootStep:rootStep; do
 module=${spec%%:*}; thm=${spec#*:}
 rg -q "^'$module\.$thm' depends on axioms:" "$task_dir/$module.log"
done
check_inputs
echo 'PASS: site-31 matched controller/physical step; controller dependencies rebuilt against physical baseline.'
