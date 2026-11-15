#!/usr/bin/env bash
set -euo pipefail
repo=$1
generic_baseline=$2
sim_baseline=$3
interface_baseline=$4
existential_baseline=$5
qfexist_baseline=$6
separation_baseline=$7
axiom_baseline=$8
forward_baseline=$9
reverse_baseline=${10}
all_baseline=${11}
fresh_baseline=${12}
obs_baseline=${13}
full_baseline=${14}
out=${15}
source_dir=$(cd -- "$(dirname -- "$0")" && pwd)
mkdir -p "$out"
cd "$repo"
lake_path=$(lake env printenv LEAN_PATH)
export LEAN_PATH="$out:$generic_baseline:$sim_baseline:$interface_baseline:$existential_baseline:$qfexist_baseline:$separation_baseline:$axiom_baseline:$forward_baseline:$reverse_baseline:$all_baseline:$fresh_baseline:$obs_baseline:$full_baseline:$lake_path"
for module in PA194ModelClosedSepClassifier PA194ClosedSepClassifierAudit; do
  lean -j1 -R "$source_dir" -M 7000 -o "$out/$module.olean" "$source_dir/$module.lean" > "$out/$module.log" 2>&1
  if rg -q "sorryAx|declaration uses 'sorry'" "$out/$module.log"; then exit 1; fi
done
count=$(rg -c 'depends on axioms:' "$out/PA194ClosedSepClassifierAudit.log")
if [[ "$count" -ne 7 ]]; then exit 1; fi
