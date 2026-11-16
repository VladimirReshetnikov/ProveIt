#!/usr/bin/env bash
# Compile the modules of this directory with every standalone module they import, one lean
# process at a time. Arguments are passed on to check_bridge.py (for example --out DIR to
# reuse compiled objects). PA194SourceArithmetic imports the other twelve modules, so one run
# compiles all thirteen; the number of axiom reports of each is checked from its log.
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
if command -v py >/dev/null 2>&1; then py=py; else py=python3; fi
also=()
for entry in PA194SourceModelBase:5 PA194SourcePredecessor:4 PA194SourceModelIso:2 \
    PA194SourceInduction:4 PA194SourceKnown:2 PA194SourceAddCoherence:3 \
    PA194SourceMulCoherence:3 PA194SourceAddComm:4 PA194SourceCalibration:3 \
    PA194SourceSets:4 PA194SourceIsoFacts:5 PA194SourceTotality:4; do
  also+=(--also "$entry")
done
"$py" -X utf8 -B "$here/../pa194-model-fairness/check_bridge.py" \
  --top "$here/PA194SourceArithmetic.lean" --reports 5 "${also[@]}" "$@"
