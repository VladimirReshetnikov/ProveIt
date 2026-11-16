#!/usr/bin/env bash
set -euo pipefail
framework_root=$(CDPATH='' cd -- "$(dirname -- "$0")" && pwd)
cd "$framework_root"
target=${1:-all}
case "$target" in
  paper|lean|checks|all) ;;
  *) printf '%s\n' 'Usage: ./build.sh [paper|lean|checks|all]' >&2; exit 2 ;;
esac
mkdir -p validation verification
if [[ "$target" == paper || "$target" == all ]]; then
  bash paper/build.sh
fi
if [[ "$target" == lean || "$target" == all ]]; then
  bash lean/build.sh
fi
if [[ "$target" == checks || "$target" == all ]]; then
  python3 code/finite_windows.py
  python3 code/series_contract.py --output verification/series_checks.json
  python3 code/chart_producer.py
  python3 code/power_gap.py
fi
