#!/usr/bin/env bash
set -euo pipefail
repo=$1
fairness_baseline=$2
generic_baseline=$3
refutation_baseline=$4
sim_baseline=$5
interface_baseline=$6
existential_baseline=$7
qfexist_baseline=$8
axiom_baseline=$9
forward_baseline=${10}
reverse_baseline=${11}
all_baseline=${12}
fresh_baseline=${13}
obs_baseline=${14}
full_baseline=${15}
out=${16}
source_dir=$(cd -- "$(dirname -- "$0")" && pwd)
mkdir -p "$out"
cd "$repo"
lake_path=$(lake env printenv LEAN_PATH)
export LEAN_PATH="$out:$fairness_baseline:$generic_baseline:$refutation_baseline:$sim_baseline:$interface_baseline:$existential_baseline:$qfexist_baseline:$axiom_baseline:$forward_baseline:$reverse_baseline:$all_baseline:$fresh_baseline:$obs_baseline:$full_baseline:$lake_path"
for module in PA194ModelAdjunctiveHalt PA194ModelNumericalSeedHalt PA194CompiledHaltAudit; do
  lean -j1 -R "$source_dir" -M 7000 -o "$out/$module.olean" "$source_dir/$module.lean" > "$out/$module.log" 2>&1
  if rg -q "sorryAx|declaration uses 'sorry'" "$out/$module.log"; then exit 1; fi
done
count=$(rg -c 'depends on axioms:' "$out/PA194CompiledHaltAudit.log")
if [[ "$count" -ne 4 ]]; then exit 1; fi
