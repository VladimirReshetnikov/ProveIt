#!/usr/bin/env bash
set -euo pipefail
cd -- "$(dirname -- "$0")/.."
lean_executable="${LEAN_BIN:-lean}"
mkdir -p validation
"$lean_executable" --version > validation/lean_version.txt
for item in FiniteTopology MetricBlueprint AlgebraicBlueprint DimensionBlueprint SphereBlueprint; do
  "$lean_executable" "lean/${item}.lean" > "validation/${item}_checked.log" 2>&1
done
python3 code/audit_sources.py

