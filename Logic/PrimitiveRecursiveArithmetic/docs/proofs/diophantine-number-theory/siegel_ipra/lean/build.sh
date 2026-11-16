#!/usr/bin/env bash
set -euo pipefail
SIEGEL_LEAN_BIN="${SIEGEL_LEAN_BIN:-lean}"
SIEGEL_SOURCE_DIR="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"
cd "$SIEGEL_SOURCE_DIR"
mkdir -p .build ../verification
export LEAN_PATH="$SIEGEL_SOURCE_DIR/.build"
{
  "$SIEGEL_LEAN_BIN" --version
  for module in Arithmetic FiniteSearch QuarticExample Specifications; do
    "$SIEGEL_LEAN_BIN" -o ".build/$module.olean" "$module.lean"
    printf 'Compiled %s.lean\n' "$module"
  done
  "$SIEGEL_LEAN_BIN" Audit.lean
} 2>&1 | tee ../verification/lean_build.txt
