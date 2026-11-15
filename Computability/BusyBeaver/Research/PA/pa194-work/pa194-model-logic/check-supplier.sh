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
for module in PA194PAeqReopenConditional PA194PAeqOpeningQVec PA194PAeqOpeningTerm PA194PAeqOpeningFormulaRules PA194PAeqOpeningFormulaInverse PA194PAeqInductionBodySupplier PA194PAeqInductionBodySupplierAudit; do
  lean -j1 -R "$source_dir" -M 7000 -o "$out/$module.olean" "$source_dir/$module.lean" > "$out/$module.log" 2>&1
  if rg -q "sorryAx|declaration uses 'sorry'" "$out/$module.log"; then exit 1; fi
done
count=$(rg -c 'depends on axioms:' "$out/PA194PAeqInductionBodySupplierAudit.log")
[[ "$count" -eq 12 ]]
