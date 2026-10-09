#!/usr/bin/env bash
set -euo pipefail

bundle_root="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
python_cmd="${PYTHON:-python3}"
mode="${1:-help}"
final_fast="$bundle_root/snapshots/final/Topology/UnknotRecognition/fast"
mkdir -p "$bundle_root/reproduced"

run_experiment() {
  local experiment_mode="$1"
  local source_fast="$2"
  local snapshot_name="$3"
  local output_name="$4"
  "$python_cmd" -B "$bundle_root/experiments/singleton_dag_research.py" \
    "$experiment_mode" \
    --baseline-fast "$bundle_root/snapshots/baseline" \
    --current-fast "$source_fast" \
    --corpus "$bundle_root/experiments/corpus.json" \
    --snapshots "$bundle_root/reproduced/$snapshot_name" \
    --output "$bundle_root/reproduced/$output_name" \
    --sizes 16 32 64 128 256 --rounds 5
}

case "$mode" in
  tests)
    cd "$final_fast"
    "$python_cmd" -B "$bundle_root/experiments/run_test_suite.py" . \
      --output "$bundle_root/reproduced/test-suite-ledger.json"
    ;;
  focused)
    cd "$final_fast"
    "$python_cmd" -B -m unittest discover -s tests -p 'test_singleton*.py' -v
    ;;
  audit|stages|benchmark)
    run_experiment "$mode" "$final_fast" frozen-guarded "$mode-guarded.json"
    ;;
  eager)
    run_experiment audit "$bundle_root/snapshots/eager" frozen-eager audit-eager.json
    ;;
  all)
    for next_mode in tests audit stages benchmark eager; do
      bash "$bundle_root/scripts/reproduce.sh" "$next_mode"
    done
    ;;
  help|-h|--help)
    printf '%s\n' 'Usage: bash scripts/reproduce.sh {focused|tests|audit|stages|benchmark|eager|all}'
    ;;
  *)
    printf '%s\n' "Unknown mode: $mode" >&2
    exit 2
    ;;
esac
