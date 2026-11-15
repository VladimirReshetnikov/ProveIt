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
seq_dir="$repo/Computability/BusyBeaver/Research/PA/pa194-work/pa194-model-sequent"
for module in ConPASequent ConPASetSequent; do
  lean -j1 -R "$seq_dir" -M 7000 -o "$out/$module.olean" "$seq_dir/$module.lean" > "$out/$module.log" 2>&1
  if rg -q "sorryAx|declaration uses 'sorry'" "$out/$module.log"; then exit 1; fi
done
for module in PA194TranslatedAxiomRule PA194TranslatedAxiomContext PA194TranslatedSequent PA194SequentAxiomAudit; do
  lean -j1 -R "$source_dir" -M 7000 -o "$out/$module.olean" "$source_dir/$module.lean" > "$out/$module.log" 2>&1
  if rg -q "sorryAx|declaration uses 'sorry'" "$out/$module.log"; then exit 1; fi
done
count=$(rg -c 'depends on axioms:' "$out/PA194SequentAxiomAudit.log")
[[ "$count" -eq 9 ]]
