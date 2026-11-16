#!/usr/bin/env bash
set -euo pipefail
cd -- "$(dirname -- "$0")"
compiler_bin="${LEAN_BIN:-lean}"
export LEAN_PATH="$PWD${LEAN_PATH:+:$LEAN_PATH}"
mkdir -p validation
"$compiler_bin" --version > validation/lean_version.txt
for module in ObjectKernel BackwardDemand TermCompiler DemandCompiler ObjectDemand ObjectTargets LexFuel RationalRoots EliminationTargets AxiomAudit; do
  "$compiler_bin" -o "$module.olean" "$module.lean" > "validation/$module.log" 2>&1
done
if rg -n 'sorryAx|Classical.choice' validation/*.log; then
  exit 1
fi
cat validation/lean_version.txt
cat validation/AxiomAudit.log
