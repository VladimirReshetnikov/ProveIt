#!/usr/bin/env bash
set -euo pipefail
: "${PA194_PROJECT_OVERLAY:?Set PA194_PROJECT_OVERLAY to the checked physical project object directory}"
: "${IPRA_FOUNDATION_OVERLAY:?Set IPRA_FOUNDATION_OVERLAY to the checked Foundation object directory}"
repo=${PA194_REPO_ROOT:-$(git -C "$(dirname "$0")" rev-parse --show-toplevel)}
cd "$repo"
base=Computability/BusyBeaver/Research/PA/verification/pa194/ipra/machine-code
PA194_PROJECT_OVERLAY=$(realpath "$PA194_PROJECT_OVERLAY")
IPRA_FOUNDATION_OVERLAY=$(realpath "$IPRA_FOUNDATION_OVERLAY")
source_dir=${PA194_TAIL_SCAN_SOURCE_DIR:-$base}
source_dir=$(realpath "$source_dir")
printf '%s  %s\n' \
  49edecc781d86904412b86f7af5ac475719f6a982eddb69f9de3733a43c9a792 "$PA194_PROJECT_OVERLAY/PA194HalfFileScan.olean" \
  6c5605b5a35486f162b39e12697665895d9bfed51005c44c288e7ec0aaaa1f02 "$PA194_PROJECT_OVERLAY/PA194RightRows.olean" \
  aeff1f6e6b652dd0bf174cea62986781d27aca1a211b03189e3151a0d3d76374 "$PA194_PROJECT_OVERLAY/PA194SixteenTwoRuns.olean" \
  2912443816bc1dc6285f56a1b47397af7d8157d0ce528839ac12f6047c3a5ce0 "$PA194_PROJECT_OVERLAY/PA194FourteenOddTo16.olean" \
  8d4b86159d887c4dedd0ed60810a89101a2fba85f6551118353b1b0aaf49b401 "$base/PA194HalfFileScan.lean" \
  350560318aa3f7fc9f100b3a85f71ab3abdee362ed5dae4469c32f48f7755ae7 "$base/PA194RightRows.lean" \
  ef9d05798abf7c94177f0a9f47cad171dcc9141fc6eb590ae812bd7e41385e85 "$base/PA194SixteenTwoRuns.lean" \
  d21eeca71033254e0bbd4bdf6a21464b13bc561067b718affb4722a504bdeb8f "$base/PA194FourteenOddTo16.lean" | sha256sum -c
task_dir=$(mktemp -d "${TMPDIR:-/dev/shm}/pa194-half-file-tail.XXXXXXXX")
trap 'rm -rf "$task_dir"' EXIT
lean_path="$task_dir:$PA194_PROJECT_OVERLAY:$IPRA_FOUNDATION_OVERLAY:$(lake env printenv LEAN_PATH)"
for module in PA194HalfFileWithTail PA194HalfFileTwoWithTail PA194NinetyThreeReturnTwoWithTail; do
  lake env env LEAN_PATH="$lean_path" lean -R "$source_dir" -M6000 -j1 \
    -o "$task_dir/$module.olean" "$source_dir/$module.lean" | tee -a "$task_dir/axioms.log"
done
for theorem in PA194HalfFileWithTail.scanHalfBlockWithTailExact \
    PA194HalfFileTwoWithTail.scanTwoWithTailExact \
    PA194NinetyThreeReturnTwoWithTail.ninetyThreeReturnTwoWithTailExact; do
  rg -q "'$theorem' depends on axioms:" "$task_dir/axioms.log"
done
if rg -q 'sorryAx' "$task_dir/axioms.log"; then
  echo 'Unexpected sorryAx in suffix-preserving scan dependencies' >&2
  exit 1
fi
