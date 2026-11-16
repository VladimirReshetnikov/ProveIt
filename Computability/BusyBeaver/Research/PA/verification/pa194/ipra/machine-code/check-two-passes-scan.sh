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
  c21141b0b94069dd0f8f876b2d7df14a02fea5889f714d7e85097cc2d515a06d "$PA194_STARTUP_OVERLAY/PA194StartupData.olean" \
  1d6b79498c7772f370065c35e7a0f11a89ba48a0d4710c609843a6cc5c1b307c "$PA194_DENSE_OVERLAY/PA194DenseStartupData.olean" \
  8acc0fd29aca4d618652d8af8d05379fcec5ee75170d91e146662b0af0d4ab33 "$PA194_DENSE_OVERLAY/PA194DenseStartupComplete.olean" \
  54dd294b184454f11b69218f6369b7dd5a6e47f96c27d5504788a75e11a3de9a "$PA194_PARENT_OVERLAY/PA194SeedHeaderPass.olean" \
  04a23ba399c77e1eef07e74ed585969cb9162242acdc2128150ae66ac67c3ff4 "$PA194_PARENT_OVERLAY/PA194SeedHeaderDispatch.olean" \
  03a5d73abe970c1ac3af1cca3cea6f20e1b6cfb245be62f00deed6d8db4647bb "$PA194_PARENT_OVERLAY/PA194NinetyThreeReturnTwoWithTail.olean" \
  637695d1c53c7bd8b34b243f18ce5b4591ea71f25bd3e653d6a85ade46e8318b "$PA194_PARENT_OVERLAY/PA194SeedHeaderTo21.olean" \
  7d0c5de85f51eb8ebdb016e9a5b9de30d8bc942f3f256721c62df6f980bda954 "$PA194_PROJECT_OVERLAY/PA194ScanInvariant.olean" \
  6c5605b5a35486f162b39e12697665895d9bfed51005c44c288e7ec0aaaa1f02 "$PA194_PROJECT_OVERLAY/PA194RightRows.olean" \
  4b8b8097d1029e2e200dbd2b2c1fbd1fe6576ad3f7293cd40388d4626b0d5524 "$PA194_PROJECT_OVERLAY/PA194LeftOneWriteOne.olean" \
  db6c29ce3b6e943bd867631ad2043227bfe3539f4942398b33fca0f5d35ea53b "$PA194_PROJECT_OVERLAY/PA194HeaderController.olean" \
  f285a10883d330e14c389f0959c2c303955fc203e54b98c4c13c44d6706c9a88 "$PA194_PROJECT_OVERLAY/PA194OnesCommute.olean" | sha256sum -c
task_dir=$(mktemp -d "${TMPDIR:-/dev/shm}/pa194-two-header-passes.XXXXXXXX")
trap 'rm -rf "$task_dir"' EXIT
lean_path="$task_dir:$PA194_PARENT_OVERLAY:$PA194_DENSE_OVERLAY:$PA194_STARTUP_OVERLAY:$PA194_PROJECT_OVERLAY:$IPRA_FOUNDATION_OVERLAY:$(lake env printenv LEAN_PATH)"
for module in PA194SecondHeaderTo93 PA194SeedHeaderReturn22 PA194SeedHeaderTo22 PA194SecondHeaderPass PA194SecondHeaderFile PA194TwoHeaderPasses PA194ThirdHeaderTo1 PA194TwoPassesTo1 PA194TwoPassesScan; do
  lake env env LEAN_PATH="$lean_path" lean -R "$source_dir" -M6000 -j1 \
    -o "$task_dir/$module.olean" "$source_dir/$module.lean" | tee -a "$task_dir/axioms.log"
done
for theorem in PA194SecondHeaderTo93.sevenTo93 PA194SeedHeaderReturn22.returnTo24 \
    PA194SeedHeaderTo22.fiveSteps PA194SecondHeaderPass.secondHeaderPass \
    PA194SecondHeaderFile.sourceFirstPassShape PA194TwoHeaderPasses.twoPasses \
    PA194ThirdHeaderTo1.twelveSteps PA194TwoPassesTo1.twoPassesTo1 \
    PA194TwoPassesScan.twoPassesScan; do
  rg -q "'$theorem' depends on axioms:" "$task_dir/axioms.log"
done
if rg -q 'sorryAx' "$task_dir/axioms.log"; then
  echo 'Unexpected sorryAx in the two-pass proof dependencies' >&2
  exit 1
fi
