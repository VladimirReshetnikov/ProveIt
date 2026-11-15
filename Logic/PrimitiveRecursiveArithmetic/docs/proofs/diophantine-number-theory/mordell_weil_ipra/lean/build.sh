#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
mw_lean_bin="${MW_LEAN_BIN:-lean}"
"$mw_lean_bin" --version
"$mw_lean_bin" -o DescentCore.olean DescentCore.lean
"$mw_lean_bin" -o FiniteSearch.olean FiniteSearch.lean
"$mw_lean_bin" -o E1FiniteTable.olean E1FiniteTable.lean
export LEAN_PATH="$PWD${LEAN_PATH:+:$LEAN_PATH}"
"$mw_lean_bin" -o EllipticSpec.olean EllipticSpec.lean
"$mw_lean_bin" Audit.lean
"$mw_lean_bin" DescentExample.lean
