#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
export PYTHONDONTWRITEBYTECODE=1
python3 examples/check_rules.py
python3 examples/finite_rules.py
python3 categorica/finality.py
python3 topologica/collapse.py
python3 topologica/nerve_transfer.py
python3 topologica/check_small_covers.py
python3 topologica/threefold.py
python3 analytica/named_pole.py
