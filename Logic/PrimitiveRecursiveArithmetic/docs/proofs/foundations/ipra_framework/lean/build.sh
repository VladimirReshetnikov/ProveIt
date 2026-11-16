#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
framework_lean_bin="${LEAN_BIN:-lean}"
framework_modules=(ObjectKernel ObjectBridge ObjectExamples FiniteContracts)
for framework_optional in Metastability PowerGap PowerGapTargets SeriesTargets ChartProducerTargets AnalyticTargets SelectionTargets; do
  if [[ -f "$framework_optional.lean" ]]; then
    framework_modules+=("$framework_optional")
  fi
done
"$framework_lean_bin" --version
for framework_module in "${framework_modules[@]}"; do
  LEAN_PATH=".:${LEAN_PATH:-}" "$framework_lean_bin" \
    -o "$framework_module.olean" "$framework_module.lean"
done
LEAN_PATH=".:${LEAN_PATH:-}" "$framework_lean_bin" AxiomAudit.lean
