#!/usr/bin/env bash
set -euo pipefail

# Run from the repository root. The project and Foundation overlays must be
# freshly built for the current sources; individual component scripts enforce
# their own pinned inputs. All products remain in an isolated tmpfs directory.
: "${IPRA_LEAN_OVERLAY:?Set IPRA_LEAN_OVERLAY to the matching built iPRA objects}"
: "${IPRA_FOUNDATION_OVERLAY:?Set IPRA_FOUNDATION_OVERLAY to the matching built Foundation objects}"
IPRA_LEAN_OVERLAY=$(realpath "$IPRA_LEAN_OVERLAY")
IPRA_FOUNDATION_OVERLAY=$(realpath "$IPRA_FOUNDATION_OVERLAY")
export IPRA_LEAN_OVERLAY IPRA_FOUNDATION_OVERLAY
base=Computability/BusyBeaver/Research/PA
package=$base/pa194-clock-source-complete
repo=$(git rev-parse --show-toplevel)
cd "$repo"
task_dir=$(mktemp -d "${TMPDIR:-/dev/shm}/pa194-complete.XXXXXXXX")
trap 'rm -rf "$task_dir"' EXIT
mkdir -p "$task_dir/scripts" "$task_dir/merged"
python3 "$package/prepare_components.py" "$task_dir/scripts"
for name in coverage startup dense zip parent clock; do
  bash -n "$task_dir/scripts/$name.sh"
done
lean --version | rg -q 'Lean \(version 4\.32\.0'
if [[ ${1:-} == --preflight ]]; then
  echo 'Component wrappers and Lean version checked; no proofs rebuilt.'
  exit 0
fi
if (( $# )); then
  echo 'usage: check.sh [--preflight]' >&2
  exit 2
fi
printf 'Combined build repository commit: '
git rev-parse HEAD
lean --version
printf 'Placed packet, generator, and component builder provenance:\n'
packet="$base/docs/pa194_conpa_2026-11-13/construction"
sha256sum "$packet/tables/pa194.tm" \
  "$packet/tables/unfolded201.native.tm" "$packet/tables/pa194.labels.json" \
  "$packet/source/pa194.folds.json" "$packet/source/pa194.grammar.json" \
  "$packet/evidence/pa194.local-cases.json" "$base/packet_inputs.py" \
  "$base/jamesyc-upstream/pa196/PA196/Program.lean" \
  "$base/pa194-quotient/generate.py" "$base/pa194-source-tree/generate.py" \
  "$base/pa194-startup/generate.py" "$base/pa194/ipra/generate.py" \
  "$base/pa194-coverage/check.sh" "$base/pa194-startup/check.sh" \
  "$base/pa194-dense/check.sh" "$base/pa194-zip-bridge/check.sh" \
  "$base/pa194-parent-zip/check.sh" "$base/pa194/ipra/machine-code/check-endpoint.sh" \
  "$package/prepare_components.py" "$package/merge_objects.py" "$package/check.sh"
for name in coverage startup dense zip parent clock; do
  echo "Building $name in a private directory"
  export PA194_COMPONENT_DIR="$task_dir/$name"
  mkdir -p "$PA194_COMPONENT_DIR"
  bash "$task_dir/scripts/$name.sh"
done
python3 "$package/merge_objects.py" "$task_dir/merged" \
  "$task_dir/coverage" "$task_dir/startup" "$task_dir/dense" \
  "$task_dir/zip" "$task_dir/parent" "$task_dir/clock"
export LEAN_PATH="$task_dir/merged:$IPRA_LEAN_OVERLAY:$IPRA_FOUNDATION_OVERLAY:$(lake env printenv LEAN_PATH)"
compile() {
  local mod=$1 src=$2
  lean -M6000 -j1 -o "$task_dir/merged/$mod.olean" "$src" | tee -a "$task_dir/final-axioms.log"
}
compile PA194SourceHalting "$base/pa194-source-halting/PA194SourceHalting.lean"
compile PA194SeedBridge "$base/pa194-seed-bridge/PA194SeedBridge.lean"
compile PA194SeedFacts "$base/pa194-seed-bridge/PA194SeedFacts.lean"
compile PA194ClockSourceConditional "$base/pa194-clock-source/PA194ClockSourceConditional.lean"
compile PA194ClockSourceStartup "$base/pa194-clock-source-startup/PA194ClockSourceStartup.lean"
compile PA194ClockCanonical "$package/PA194ClockCanonical.lean"
compile PA194ClockSourceComplete "$package/PA194ClockSourceComplete.lean"
if rg -q 'sorryAx' "$task_dir/final-axioms.log"; then
  echo 'Unexpected sorryAx in final composition' >&2
  exit 1
fi
echo 'Completed fresh PA194 coverage, startup, and clock/source composition.'
