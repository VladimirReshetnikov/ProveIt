#!/usr/bin/env bash
set -euo pipefail

bundle_dir=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)
repository_dir=${1:-.}
python3 "$bundle_dir/tools/check_replacements.py" "$repository_dir"
cd -- "$repository_dir"

lake build \
  DiophantineConsistency.ObjectAdditionCancellation \
  DiophantineConsistency.ObjectNaturalZero \
  DiophantineConsistency.NativePellStepDown \
  DiophantineConsistency.NativePellBootstrap \
  DiophantineConsistency.MinimumNorm \
  DiophantineConsistency.NativeFieldCycles2011 \
  DiophantineConsistency.NativeFieldCycles2011Checks

lake env lean --root="$bundle_dir" "$bundle_dir/validation/AxiomAudit.lean"
lake env lean --root="$bundle_dir" "$bundle_dir/experiments/NoVacuousInduction.lean"
lake env lean --root="$bundle_dir" "$bundle_dir/experiments/PellBaseMonotonicity.lean"
lake env lean --root="$bundle_dir" "$bundle_dir/experiments/FiniteInvariant.lean"
