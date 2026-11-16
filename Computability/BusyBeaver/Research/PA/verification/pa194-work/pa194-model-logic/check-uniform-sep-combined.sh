#!/usr/bin/env bash
set -euo pipefail
repo=$1
uniform_baseline=$2
classifier_baseline=$3
generic_baseline=$4
sim_baseline=$5
interface_baseline=$6
existential_baseline=$7
qfexist_baseline=$8
separation_baseline=$9
axiom_baseline=${10}
forward_baseline=${11}
reverse_baseline=${12}
all_baseline=${13}
fresh_baseline=${14}
obs_baseline=${15}
full_baseline=${16}
out=${17}
source_dir=$(cd -- "$(dirname -- "$0")" && pwd)
mkdir -p "$out"
cd "$repo"
lake_path=$(lake env printenv LEAN_PATH)
export LEAN_PATH="$out:$uniform_baseline:$classifier_baseline:$generic_baseline:$sim_baseline:$interface_baseline:$existential_baseline:$qfexist_baseline:$separation_baseline:$axiom_baseline:$forward_baseline:$reverse_baseline:$all_baseline:$fresh_baseline:$obs_baseline:$full_baseline:$lake_path"
for module in PA194ModelSepRootGraph PA194ModelClosedSepUniform PA194UniformSepCombinedAudit; do
  lean -j1 -R "$source_dir" -M 7000 -o "$out/$module.olean" "$source_dir/$module.lean" > "$out/$module.log" 2>&1
  if rg -q "sorryAx|declaration uses 'sorry'" "$out/$module.log"; then exit 1; fi
done
count=$(rg -c 'depends on axioms:' "$out/PA194UniformSepCombinedAudit.log")
if [[ "$count" -ne 5 ]]; then exit 1; fi
