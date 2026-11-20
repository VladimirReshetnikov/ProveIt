#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
task_lake_bin="${LEAN_LAKE_BIN:-lake}"
"$task_lake_bin" env lean --version
"$task_lake_bin" build
"$task_lake_bin" env lean Audit.lean
"$task_lake_bin" env lean Examples.lean
