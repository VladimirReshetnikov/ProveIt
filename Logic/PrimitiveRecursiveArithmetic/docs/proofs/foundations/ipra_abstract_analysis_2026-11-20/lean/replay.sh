#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
lean_lake_bin="${LEAN_LAKE_BIN:-lake}"
"$lean_lake_bin" env lean --version
"$lean_lake_bin" build
"$lean_lake_bin" env lean Audit.lean
"$lean_lake_bin" env lean Examples.lean
