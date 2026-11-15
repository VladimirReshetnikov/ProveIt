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
for module in PA194PAeqND PA194PAeqNDSingle PA194PAeqNDList PA194PAeqNDShift; do
  source_path=$(rg --files Computability/BusyBeaver/Research/PA/pa194-work | rg "/${module}\.lean$")
  lean -j1 -R "$(dirname "$source_path")" -M 7000 -o "$out/$module.olean" "$source_path" > "$out/$module.log" 2>&1
  if rg -q "sorryAx|declaration uses 'sorry'" "$out/$module.log"; then exit 1; fi
done
for module in PA194PAeqAddOneProof PA194PAeqAddOneProofAudit; do
  lean -j1 -R "$source_dir" -M 7000 -o "$out/$module.olean" "$source_dir/$module.lean" > "$out/$module.log" 2>&1
  if rg -q "sorryAx|declaration uses 'sorry'" "$out/$module.log"; then exit 1; fi
done
count=$(rg -c 'depends on axioms:' "$out/PA194PAeqAddOneProofAudit.log")
[[ "$count" -eq 9 ]]
