#!/usr/bin/env bash
set -euo pipefail
if (($# != 5)); then echo "usage: $0 REPO SITE27_BASELINE PROJECT_FOUNDATION PACKAGE_FOUNDATION SOURCE" >&2; exit 2; fi
repo=$(realpath "$1")
baseline=$(realpath "$2")
project=$(realpath "$3")
package=$(realpath "$4")
source=$(realpath "$5")
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
  | sha256sum -c -
}
check_inputs
task_dir=$(mktemp -d "${TMPDIR:-/dev/shm}/pa194-site31-header.XXXXXXXX")
trap 'rm -rf "$task_dir"' EXIT
cd "$repo"
lake_path=$(lake env printenv LEAN_PATH)
export LEAN_PATH="$task_dir:$baseline:$project:$package:$lake_path"
for m in PA194Path31Header PA194Site31HeaderDispatch PA194Site31HeaderTo49 PA194Site31HeaderTo84 PA194Site31HeaderTo17 PA194Site31HeaderReturn PA194Site31HeaderPass PA194Site31HeaderPassPath PA194Site31MarkedTo106 PA194Site31To71 PA194Site31SecondTo17 PA194Site31SecondReturn PA194Site31SecondUnmark PA194Site31SecondRoot; do
 case "$m" in
  PA194Path31Header) cp "$repo/Computability/BusyBeaver/Research/PA/verification/pa194/ipra/machine-code/$m.lean" "$task_dir/$m.lean" ;;
  *) cp "$source/$m.lean" "$task_dir/$m.lean" ;;
 esac
 echo "Checking $m"
 lake env env LEAN_PATH="$LEAN_PATH" lean -M6000 -j1 -R "$task_dir" -o "$task_dir/$m.olean" "$task_dir/$m.lean" 2>&1 | tee "$task_dir/$m.log"
 if rg -q 'sorryAx' "$task_dir/$m.log"; then echo 'Unexpected sorryAx' >&2; exit 1; fi
done
for spec in PA194Path31Header:path31 PA194Site31HeaderDispatch:row63one PA194Site31HeaderDispatch:row89zero PA194Site31HeaderDispatch:sevenSteps PA194Site31HeaderTo49:row46odd PA194Site31HeaderTo49:row65one PA194Site31HeaderTo49:path31Input PA194Site31HeaderTo49:to49 PA194Site31HeaderTo84:fiveSteps PA194Site31HeaderTo84:to84 PA194Site31HeaderTo17:site31HeaderTo17 PA194Site31HeaderReturn:returnTo24 PA194Site31HeaderPass:site31HeaderPass PA194Site31HeaderPassPath:firstPass PA194Site31MarkedTo106:markedTo106 PA194Site31To71:site31To71 PA194Site31SecondTo17:site31SecondTo17 PA194Site31SecondReturn:return17To24 PA194Site31SecondUnmark:unmarkTo24 PA194Site31SecondRoot:site31SecondRoot; do
 module=${spec%%:*}; thm=${spec#*:}
 rg -q "^'$module\.$thm' depends on axioms:" "$task_dir/$module.log"
done
check_inputs
echo 'PASS: site-31 physical second root pass; staged machine/foundation roots remain prebuilt.'
