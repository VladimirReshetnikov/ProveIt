#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
python3 code/check_density_certificate.py --output data/density_certificate.json
python3 code/verify_rank_moments.py --output data/rank_moments_results.json
python3 code/conductor23_benchmark.py --limit 2000 --output data/conductor23_rerun
