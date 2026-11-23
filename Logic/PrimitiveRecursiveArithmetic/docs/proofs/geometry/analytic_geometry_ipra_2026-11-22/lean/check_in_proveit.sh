#!/usr/bin/env bash
set -euo pipefail

if [[ $# -ne 1 ]]; then
  echo 'Usage: check_in_proveit.sh /absolute/path/to/ProveIt' >&2
  exit 2
fi

packet_lean_dir="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"
proveit_dir="$1"
expected_revision='bbb85238dac533fc4b7b84a750cca864fe35fed5'
actual_revision="$(git -C "$proveit_dir" rev-parse HEAD)"
if [[ "$actual_revision" != "$expected_revision" ]]; then
  echo "Revision mismatch: expected $expected_revision; found $actual_revision" >&2
  exit 3
fi

cd -- "$proveit_dir"
command -v lake >/dev/null
lake env lean --version
lake build IPRADerivations

# The complete Mathlib import in ExactCodes requires its root module to exist.
# In a standard cached dependency installation this target is already present.
lake build Mathlib

lake env lean "$packet_lean_dir/ObjectCertificates.lean" \
  | tee "$packet_lean_dir/ObjectCertificates.build.log"
lake env lean "$packet_lean_dir/ExactCodes.lean" \
  | tee "$packet_lean_dir/ExactCodes.build.log"
lake env lean "$packet_lean_dir/BridgeSpec.lean" \
  | tee "$packet_lean_dir/BridgeSpec.build.log"
lake env lean "$packet_lean_dir/AnalyticPrograms.lean" \
  | tee "$packet_lean_dir/AnalyticPrograms.build.log"

echo 'All four files typechecked. Review printed axiom dependencies before reporting verification.'
