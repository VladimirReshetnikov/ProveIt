#!/usr/bin/env bash
set -euo pipefail
if [[ $# -ne 1 ]]; then
  echo "Usage: bash scripts/replay_kernels.sh /path/to/ProveIt" >&2
  exit 2
fi
artifact_root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)
task_repo=$(cd -- "$1" && pwd)
task_output=$(mktemp -d -t proveit-proof-kernels-XXXXXXXX)
trap 'rm -rf -- "$task_output"' EXIT
cd -- "$task_repo"
lake build DiophantineConsistency.Representation DiophantineConsistency.ArithmeticRepresentation
task_lean=$(lake env which lean)
task_base_path=$(lake env printenv LEAN_PATH)
export LEAN_PATH="$task_output:$task_base_path"
mkdir -p "$task_output/DiophantineConsistency"
task_sources="$artifact_root/replacements/Computability/DiophantineConsistency/Lean/DiophantineConsistency"
for task_module in ComposeRepresentation DirectComposition SyntaxCoefficients; do
  "$task_lean" "$task_sources/$task_module.lean" \
    -o "$task_output/DiophantineConsistency/$task_module.olean"
done
for task_kernel in CarrierKernels StructuralKernels JonesBridgeHarness CompositionCompatibility; do
  "$task_lean" "$artifact_root/lean/$task_kernel.lean"
done
echo "Completed the limited module/kernel replay described in the report."
