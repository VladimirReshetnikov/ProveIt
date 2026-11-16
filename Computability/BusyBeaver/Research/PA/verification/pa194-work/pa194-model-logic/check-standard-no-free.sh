#!/usr/bin/env bash
set -euo pipefail
repo=$1
classifier_baseline=$2
generic_baseline=$3
sim_baseline=$4
interface_baseline=$5
existential_baseline=$6
qfexist_baseline=$7
separation_baseline=$8
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
export LEAN_PATH="$out:$classifier_baseline:$generic_baseline:$sim_baseline:$interface_baseline:$existential_baseline:$qfexist_baseline:$separation_baseline:$axiom_baseline:$forward_baseline:$reverse_baseline:$all_baseline:$fresh_baseline:$obs_baseline:$full_baseline:$lake_path"
for module in PA194ModelStandardNoFree PA194StandardNoFreeAudit; do
  lean -j1 -R "$source_dir" -M 7000 -o "$out/$module.olean" "$source_dir/$module.lean" > "$out/$module.log" 2>&1
  if rg -q "sorryAx|declaration uses 'sorry'" "$out/$module.log"; then exit 1; fi
done
count=$(rg -c 'depends on axioms:' "$out/PA194StandardNoFreeAudit.log")
if [[ "$count" -ne 4 ]]; then exit 1; fi
