#!/usr/bin/env bash
set -euo pipefail
repo=$1
out=$2
shift 2
source_dir=$(cd -- "$(dirname -- "$0")" && pwd)
mkdir -p "$out"
cd "$repo"
lake_path=$(lake env printenv LEAN_PATH)
baselines=$(IFS=:; printf '%s' "$*")
export LEAN_PATH="$out:$baselines:$lake_path"
for module in PA194PAeqUnbindTerm PA194PAeqUnbindTermInverse PA194PAeqUnbindFormula PA194PAeqUnbindFormulaInverse PA194PAeqClosureComplexity PA194PAeqUncloseHistory PA194PAeqInductionEnvelope PA194PAeqInductionUniform PA194PAeqStandardNoFree PA194PAeqInductionTheory PA194PAeqInductionTheoryTyped; do
  lean -j1 -R "$source_dir" -M 7000 -o "$out/$module.olean" "$source_dir/$module.lean" > "$out/$module.log" 2>&1
  if rg -q "sorryAx|declaration uses 'sorry'" "$out/$module.log"; then exit 1; fi
done
inventory_dir="$repo/Computability/BusyBeaver/Research/PA/pa194-work/pa194-paeq-target-inventory"
lean -j1 -R "$inventory_dir" -M 7000 -o "$out/PA194PAeqTargetAxiom.olean" "$inventory_dir/PA194PAeqTargetAxiom.lean" > "$out/PA194PAeqTargetAxiom.log" 2>&1
if rg -q "sorryAx|declaration uses 'sorry'" "$out/PA194PAeqTargetAxiom.log"; then exit 1; fi
for module in PA194PAeqOrdinaryTheoryDelta PA194PAeqOrdinaryTheoryClass PA194PAeqOrdinaryDeltaAudit; do
  lean -j1 -R "$source_dir" -M 7000 -o "$out/$module.olean" "$source_dir/$module.lean" > "$out/$module.log" 2>&1
  if rg -q "sorryAx|declaration uses 'sorry'" "$out/$module.log"; then exit 1; fi
done
count=$(rg -c 'depends on axioms:' "$out/PA194PAeqOrdinaryDeltaAudit.log")
[[ "$count" -eq 20 ]]
