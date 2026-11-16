#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
lean_bin="${LEAN_BIN:-lean}"
"$lean_bin" --version
"$lean_bin" FiniteObservation.lean
"$lean_bin" Targets.lean
