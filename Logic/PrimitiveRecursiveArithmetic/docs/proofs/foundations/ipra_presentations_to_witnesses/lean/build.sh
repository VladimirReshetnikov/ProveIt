#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
: "${LEAN_BIN:=lean}"
mkdir -p .build
export LEAN_PATH="$PWD/.build"
"$LEAN_BIN" --version
for module in ObjectKernel ObjectFusion ObjectSimulation SquaringTransport PrimitiveEigenvalue EigenvalueBound FiniteAlgebraTargets FiniteAlgebraExamples; do
  printf 'Checking %s.lean\n' "$module"
  "$LEAN_BIN" -o ".build/$module.olean" "$module.lean"
done
