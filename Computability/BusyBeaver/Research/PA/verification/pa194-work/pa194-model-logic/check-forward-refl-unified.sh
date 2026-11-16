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
foundation_dir="$repo/Computability/BusyBeaver/Research/PA/verification/pa194-work/pa194-foundation-identity-empty"
lean -j1 -R "$foundation_dir" -M 7000 -o "$out/PA194FoundationOrderIso.olean" "$foundation_dir/PA194FoundationOrderIso.lean" > "$out/PA194FoundationOrderIso.log" 2>&1
if rg -q "sorryAx|declaration uses 'sorry'" "$out/PA194FoundationOrderIso.log"; then exit 1; fi
for module in PA194AtomicPAeq PA194FormulaDispatcher PA194FormulaDispatcherEquations PA194FormulaScope PA194BinaryTypedQuote PA194ForwardTyped PA194ForwardReflProof PA194ForwardReflContext PA194ForwardReflUnifiedAudit; do
  lean -j1 -R "$source_dir" -M 7000 -o "$out/$module.olean" "$source_dir/$module.lean" > "$out/$module.log" 2>&1
  if rg -q "sorryAx|declaration uses 'sorry'" "$out/$module.log"; then exit 1; fi
done
count=$(rg -c 'depends on axioms:' "$out/PA194ForwardReflUnifiedAudit.log")
[[ "$count" -eq 7 ]]
