#!/usr/bin/env bash
set -euo pipefail
: "${PA194_PARENT_OVERLAY:?Set to a checked overlay containing first-pass and arbitrary-tail-scan modules}"
: "${PA194_PROJECT_OVERLAY:?Set to the checked physical project object directory}"
: "${PA194_STARTUP_OVERLAY:?Set to the checked parent-startup object directory}"
: "${PA194_DENSE_OVERLAY:?Set to the checked dense-startup object directory}"
: "${IPRA_FOUNDATION_OVERLAY:?Set to the checked Foundation object directory}"
repo=${PA194_REPO_ROOT:-$(git -C "$(dirname "$0")" rev-parse --show-toplevel)}
cd "$repo"
base=Computability/BusyBeaver/Research/PA/verification/pa194/ipra/machine-code
source_dir=${PA194_TWO_PASSES_SOURCE_DIR:-$base}
source_dir=$(realpath "$source_dir")
PA194_PARENT_OVERLAY=$(realpath "$PA194_PARENT_OVERLAY")
PA194_PROJECT_OVERLAY=$(realpath "$PA194_PROJECT_OVERLAY")
PA194_STARTUP_OVERLAY=$(realpath "$PA194_STARTUP_OVERLAY")
PA194_DENSE_OVERLAY=$(realpath "$PA194_DENSE_OVERLAY")
IPRA_FOUNDATION_OVERLAY=$(realpath "$IPRA_FOUNDATION_OVERLAY")
printf '%s  %s\n' \
  382135ae061e88ad738564f356f012a3acded7065d55c18601b42f9293bb702f "$PA194_STARTUP_OVERLAY/PA194SourceProgram.olean" \
  c21141b0b94069dd0f8f876b2d7df14a02fea5889f714d7e85097cc2d515a06d "$PA194_STARTUP_OVERLAY/PA194StartupData.olean" \
  1d6b79498c7772f370065c35e7a0f11a89ba48a0d4710c609843a6cc5c1b307c "$PA194_DENSE_OVERLAY/PA194DenseStartupData.olean" \
  8acc0fd29aca4d618652d8af8d05379fcec5ee75170d91e146662b0af0d4ab33 "$PA194_DENSE_OVERLAY/PA194DenseStartupComplete.olean" \
  dd3016db7c7b7c5d6fadaeb08b9f579d4e7302f968945571b8364f996e1c5bf1 "$PA194_PARENT_OVERLAY/PA194HalfFileWithTail.olean" \
  eb41480ae7181a1c35fbdba5b58c8e3efd24488e1c25b2af78a2936015c6a451 "$PA194_PARENT_OVERLAY/PA194ZeroReturnFrom16.olean" \
  54dd294b184454f11b69218f6369b7dd5a6e47f96c27d5504788a75e11a3de9a "$PA194_PARENT_OVERLAY/PA194SeedHeaderPass.olean" \
  04a23ba399c77e1eef07e74ed585969cb9162242acdc2128150ae66ac67c3ff4 "$PA194_PARENT_OVERLAY/PA194SeedHeaderDispatch.olean" \
  03a5d73abe970c1ac3af1cca3cea6f20e1b6cfb245be62f00deed6d8db4647bb "$PA194_PARENT_OVERLAY/PA194NinetyThreeReturnTwoWithTail.olean" \
  637695d1c53c7bd8b34b243f18ce5b4591ea71f25bd3e653d6a85ade46e8318b "$PA194_PARENT_OVERLAY/PA194SeedHeaderTo21.olean" \
  7d0c5de85f51eb8ebdb016e9a5b9de30d8bc942f3f256721c62df6f980bda954 "$PA194_PROJECT_OVERLAY/PA194ScanInvariant.olean" \
  9cdafc2ab2ca29f39b0c3aa2432a5cb8004a750bdcc74e95701d3fc0096587d9 "$PA194_PROJECT_OVERLAY/PA194RollbackCell.olean" \
  9599561dcbf523a984c0761216d525e8f689dedda34fd04e6c1417c0fa05b776 "$PA194_PROJECT_OVERLAY/PA194DecrementZeroCell.olean" \
  6b028991a3513d5e90349039ef70b79671079bc48c8b7b5972afa37242faeba3 "$PA194_PROJECT_OVERLAY/PA194ThirteenExitComposition.olean" \
  15b06d381552d4fc29e279c18a09d0098a36adc5a91cacd86b1ff4482fb4c8ad "$PA194_PROJECT_OVERLAY/PA194FirstThreeBlankTailTo16.olean" \
  d0b919b72411d6c865586d104fcd75f062572f9afe9b4a85975f39f621c76c6b "$PA194_PROJECT_OVERLAY/PA194ZerosDouble.olean" \
  056e1ae21b02f2b7b28f2d474274e53fffaef911b1f230eb3eeccc4696b9745c "$PA194_PROJECT_OVERLAY/PA194RegisterPermutation.olean" \
  649cf131270987b286861068342bdefdeace0de430c4a4c3013765299b5e2404 "$PA194_PROJECT_OVERLAY/PA194UnaryRuns.olean" \
  4848652b78db7da2d38e78e80cbaedf1df18f49ce31c3be0ab9623e46e49444c "$PA194_PROJECT_OVERLAY/PA194ZeroRuns.olean" \
  5d7025d3559f4b46477b3c311071d8d06c36ff4ec28697c454bbb87c1fd60104 "$PA194_PROJECT_OVERLAY/DiophantineConsistency/PRAOpenInduction.olean" \
  bb719590f351de5ddab9603b3b9a9299590004b75bb7602aeb1dfaba84ab7bcf "$PA194_PROJECT_OVERLAY/PA194EightyFourTo17.olean" \
  361f22d6606683c4cb9e6aa36aa19fbe8823302f7e2ed32afbdbdb95e8ad7786 "$PA194_PROJECT_OVERLAY/PA194GenericRightScan.olean" \
  cebf3ec87337969f17704ec2885bcfdab1ef9cc56f1d9599990087ce293e0473 "$PA194_PROJECT_OVERLAY/PA194RewindFile.olean" \
  8aefa49ec2b82e7e4fdf26f97625afdd52984d0b0010efd782df058c490ff5a8 "$PA194_PROJECT_OVERLAY/PA194FileTraversalMeaning.olean" \
  c23d3d978972b438d6d7bdcabc87bc15f86c861af68248d645dd55c9904c79af "$PA194_PROJECT_OVERLAY/PA194RewindFirst.olean" \
  5415e0aa9ba76acb85b4a37ebd5df90a2337ad1e5536f9eee6de3285a8528076 "$PA194_PROJECT_OVERLAY/PA194ReturnFileMeaning.olean" \
  6c5605b5a35486f162b39e12697665895d9bfed51005c44c288e7ec0aaaa1f02 "$PA194_PROJECT_OVERLAY/PA194RightRows.olean" \
  4b8b8097d1029e2e200dbd2b2c1fbd1fe6576ad3f7293cd40388d4626b0d5524 "$PA194_PROJECT_OVERLAY/PA194LeftOneWriteOne.olean" \
  db6c29ce3b6e943bd867631ad2043227bfe3539f4942398b33fca0f5d35ea53b "$PA194_PROJECT_OVERLAY/PA194HeaderController.olean" \
  f285a10883d330e14c389f0959c2c303955fc203e54b98c4c13c44d6706c9a88 "$PA194_PROJECT_OVERLAY/PA194OnesCommute.olean" | sha256sum -c
task_dir=$(mktemp -d "${TMPDIR:-/dev/shm}/pa194-two-header-passes.XXXXXXXX")
trap 'rm -rf "$task_dir"' EXIT
lean_path="$task_dir:$PA194_PARENT_OVERLAY:$PA194_DENSE_OVERLAY:$PA194_STARTUP_OVERLAY:$PA194_PROJECT_OVERLAY:$IPRA_FOUNDATION_OVERLAY:$(lake env printenv LEAN_PATH)"
for module in PA194Site27HeaderDispatch PA194Site27HeaderTo17 PA194Site27HeaderReturn PA194Site27HeaderPass PA194Site27SecondDispatch PA194Site27To106 PA194Site27Scan106 PA194Site27To71 PA194HalfFileSixWithTail PA194Site27To14 PA194SixRewind PA194Site27ScanRewind PA194Site27To17; do
  lake env env LEAN_PATH="$lean_path" lean -R "$source_dir" -M6000 -j1 \
    -o "$task_dir/$module.olean" "$source_dir/$module.lean" | tee -a "$task_dir/axioms.log"
done
for theorem in PA194Site27HeaderDispatch.thirteenSteps PA194Site27HeaderTo17.site27HeaderTo17 \
    PA194Site27HeaderReturn.returnTo24 PA194Site27HeaderPass.site27HeaderPass \
    PA194Site27SecondDispatch.eightTo106 PA194Site27To106.site27To106 \
    PA194Site27Scan106.scan106To71 PA194Site27To71.site27To71 \
    PA194HalfFileSixWithTail.scanSixExact PA194Site27To14.site27To14 \
    PA194SixRewind.sixTo17 PA194Site27ScanRewind.scanAndRewind PA194Site27To17.site27To17; do
  rg -q "'$theorem' depends on axioms:" "$task_dir/axioms.log"
done
if rg -q 'sorryAx' "$task_dir/axioms.log"; then
  echo 'Unexpected sorryAx in the two-pass proof dependencies' >&2
  exit 1
fi
