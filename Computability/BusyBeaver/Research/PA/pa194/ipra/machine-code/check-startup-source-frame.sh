#!/usr/bin/env bash
set -euo pipefail
: "${PA194_BRIDGE_OVERLAY:?Set PA194_BRIDGE_OVERLAY to the checked standard/model bridge object directory}"
: "${PA194_DENSE_OVERLAY:?Set PA194_DENSE_OVERLAY to the checked literal dense-startup object directory}"
: "${PA194_PARENT_OVERLAY:?Set PA194_PARENT_OVERLAY to the checked source-seed object directory}"
: "${PA194_PROJECT_OVERLAY:?Set PA194_PROJECT_OVERLAY to the checked physical/source project object directory}"
: "${IPRA_FOUNDATION_OVERLAY:?Set IPRA_FOUNDATION_OVERLAY to the checked Foundation object directory}"
repo=${PA194_REPO_ROOT:-$(git -C "$(dirname "$0")" rev-parse --show-toplevel)}
cd "$repo"
base=Computability/BusyBeaver/Research/PA/pa194/ipra/machine-code
PA194_BRIDGE_OVERLAY=$(realpath "$PA194_BRIDGE_OVERLAY")
PA194_DENSE_OVERLAY=$(realpath "$PA194_DENSE_OVERLAY")
PA194_PARENT_OVERLAY=$(realpath "$PA194_PARENT_OVERLAY")
PA194_PROJECT_OVERLAY=$(realpath "$PA194_PROJECT_OVERLAY")
IPRA_FOUNDATION_OVERLAY=$(realpath "$IPRA_FOUNDATION_OVERLAY")
source=${PA194_SOURCE_FRAME_SOURCE:-$base/PA194StartupSourceFrame.lean}
source=$(realpath "$source")
sha256sum -c <<'PINS'
e92eb3008afc79eb9e2893c1339f97d298aca3dd472288e8d5caf4d0291e4e1a  Computability/BusyBeaver/Research/PA/pa194/ipra/machine-code/PA194RegisterFileStandard.lean
df44bda615a0c9b81d0ee5c6398f74b176fa626f50ed77f448342918d134671f  Computability/BusyBeaver/Research/PA/pa194/ipra/machine-code/PA194RegisterPermutation.lean
8cdec8d14fd7c20ce7d41c456d08686b15a0fe751471fca8edaac04d5934fabc  Computability/BusyBeaver/Research/PA/pa194/ipra/machine-code/PA194ZeroRuns.lean
10ab712487d4d32082f950533885cb5d7ab814bc6bbc82c8efa18416a6919527  Computability/BusyBeaver/Research/PA/pa194/ipra/machine-code/PA194StateOne.lean
f80a20725cc4f2c782e7492e22a8298ce4413ab6c557b74c267e12be01b48876  Computability/BusyBeaver/Research/PA/pa194-work/pa194-command-source/PA194FetchPrefixBinding.lean
PINS
printf '%s  %s\n' \
  9b95bd956b0f0b626f9d2f0ba61ff882a743875d7a316b6c5647f6309432f219 "$PA194_BRIDGE_OVERLAY/PA194ModelDenseStartup.olean" \
  998d1add0e4e002443e714666966e3e609396fe11063d2e2858ec720f3416605 "$PA194_BRIDGE_OVERLAY/PA194StandardCodeBridge.olean" \
  8acc0fd29aca4d618652d8af8d05379fcec5ee75170d91e146662b0af0d4ab33 "$PA194_DENSE_OVERLAY/PA194DenseStartupComplete.olean" \
  c21141b0b94069dd0f8f876b2d7df14a02fea5889f714d7e85097cc2d515a06d "$PA194_PARENT_OVERLAY/PA194StartupData.olean" \
  26f433ab8534e17c909ad6f62fbc5e8dfbacc4a6f72fe398e6ce6f8c4c66a05e "$PA194_PROJECT_OVERLAY/PA194RegisterFileStandard.olean" \
  056e1ae21b02f2b7b28f2d474274e53fffaef911b1f230eb3eeccc4696b9745c "$PA194_PROJECT_OVERLAY/PA194RegisterPermutation.olean" \
  4848652b78db7da2d38e78e80cbaedf1df18f49ce31c3be0ab9623e46e49444c "$PA194_PROJECT_OVERLAY/PA194ZeroRuns.olean" \
  7188c01a8a69007f6963186593c316729e9773651004fe010f6cea5650795160 "$PA194_PROJECT_OVERLAY/PA194StateOne.olean" \
  7a3d21ba56d7cd7c6e9494b9390626db9e296ce362abeb05fb6f98b5f40af9c4 "$PA194_PROJECT_OVERLAY/PA194FetchPrefixBinding.olean" | sha256sum -c
task_dir=$(mktemp -d "${TMPDIR:-/dev/shm}/pa194-startup-source-frame.XXXXXXXX")
trap 'rm -rf "$task_dir"' EXIT
lean_path="$task_dir:$PA194_DENSE_OVERLAY:$PA194_BRIDGE_OVERLAY:$PA194_PARENT_OVERLAY:$PA194_PROJECT_OVERLAY:$IPRA_FOUNDATION_OVERLAY:$(lake env printenv LEAN_PATH)"
lake env env LEAN_PATH="$lean_path" lean -R "$(dirname "$source")" -M6000 -j1 \
  -o "$task_dir/PA194StartupSourceFrame.olean" "$source" | tee "$task_dir/axioms.log"
for name in firstSeedSourceStep seedArgs_logical modelSourceSeed seedRight_sourceLayout modelDenseStartupSourceFrame; do
  rg -q "'PA194StartupSourceFrame\.$name' depends on axioms:" "$task_dir/axioms.log"
done
if rg -q 'sorryAx' "$task_dir/axioms.log"; then
  echo 'Unexpected sorryAx in startup source-frame theorem dependencies' >&2
  exit 1
fi
