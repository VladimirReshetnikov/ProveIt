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
inventory_dir="$repo/Computability/BusyBeaver/Research/PA/verification/pa194-work/pa194-paeq-target-inventory"
lean -j1 -R "$inventory_dir" -M 7000 -o "$out/PA194PAeqTargetInventory.olean" "$inventory_dir/PA194PAeqTargetInventory.lean" > "$out/PA194PAeqTargetInventory.log" 2>&1
for module in PA194PAeqInductionCode PA194PAeqClosedInduction PA194PAeqInductionCodeAudit; do
  lean -j1 -R "$source_dir" -M 7000 -o "$out/$module.olean" "$source_dir/$module.lean" > "$out/$module.log" 2>&1
  if rg -q "sorryAx|declaration uses 'sorry'" "$out/$module.log"; then exit 1; fi
done
count=$(rg -c 'depends on axioms:' "$out/PA194PAeqInductionCodeAudit.log")
[[ "$count" -eq 6 ]]
