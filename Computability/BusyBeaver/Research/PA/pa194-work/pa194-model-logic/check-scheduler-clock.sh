#!/usr/bin/env bash
set -euo pipefail
repo=$1
out=$2
namespace_baseline=$3
shift 3
source_dir=$(cd -- "$(dirname -- "$0")" && pwd)
mkdir -p "$out"
ln -s "$namespace_baseline/PA196" "$out/PA196"
ln -s "$namespace_baseline/M6" "$out/M6"
cd "$repo"
lake_path=$(lake env printenv LEAN_PATH)
baselines=$(IFS=:; printf '%s' "$*")
export LEAN_PATH="$out:$baselines:$lake_path"
for module in PA194SchedulerClockBridge PA194SchedulerClockBridgeAudit; do
  lean -j1 -R "$source_dir" -M 7000 -o "$out/$module.olean" "$source_dir/$module.lean" > "$out/$module.log" 2>&1
  if rg -q "sorryAx|declaration uses 'sorry'" "$out/$module.log"; then exit 1; fi
done
count=$(rg -c 'depends on axioms:' "$out/PA194SchedulerClockBridgeAudit.log")
[[ "$count" -eq 2 ]]
