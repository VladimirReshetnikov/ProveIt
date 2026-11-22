#!/usr/bin/env bash
set -euo pipefail

# Usage: ./check_against_proveit.sh /absolute/path/to/pinned/ProveIt
# This script only compiles local files. It does not fetch or mutate Git.
if [ "$#" -ne 1 ]; then
  echo "Usage: $0 /absolute/path/to/ProveIt" >&2
  exit 2
fi
proveit_root="$1"
script_root="$(cd -- "$(dirname -- "$0")" && pwd)"
pinned_ref="3ee850b4c2d650cf01263823fd5415963747c5d0"
actual_ref="$(git -C "$proveit_root" rev-parse HEAD)"
if [ "$actual_ref" != "$pinned_ref" ]; then
  echo "Expected ProveIt revision $pinned_ref; found $actual_ref" >&2
  exit 3
fi
cd -- "$proveit_root"
lake build +IPRADerivations.Foundations.StrongConvexity
lake build +IPRADerivations.Core.OrderCertificates
lake build +IPRADerivations.Analysis.GaussianPolynomialMonicNorm
lake build +IPRADerivations.Analysis.GaussianRationalTranslation
lake build +IPRADerivations.Core.Gcd
lake env lean "$script_root/QuantitativeElimination/MidpointCancellation.lean"
lake env lean "$script_root/QuantitativeElimination/RuntimeNormTargets.lean"

lake env lean "$script_root/SemanticSquarefreeTargets.lean"
