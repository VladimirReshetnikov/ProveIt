#!/usr/bin/env bash
set -euo pipefail
repo=$1
foundation_lib=$2
workspace_lib=$3
diophantine_lib=$4
out=$5
mkdir -p "$out"
ln -s "$foundation_lib/Foundation" "$out/Foundation"
ln -s "$workspace_lib/BusyBeaver" "$out/BusyBeaver"
ln -s "$workspace_lib/FirstOrder" "$out/FirstOrder"
ln -s "$diophantine_lib/DiophantineConsistency" "$out/DiophantineConsistency"
cd "$repo"
python3 -u Computability/BusyBeaver/Research/PA/pa194-work/pa194-model-fairness/check_bridge.py --out "$out"
