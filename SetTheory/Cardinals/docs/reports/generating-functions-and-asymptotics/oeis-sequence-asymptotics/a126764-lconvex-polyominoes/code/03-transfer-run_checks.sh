#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
python checks/multiplier/derive_multiplier.py
python checks/symbolic/check_inverse.py
(cd checks/exact && python verify_exact.py --max-n 8000 --literal-n 400 --output verification_replay.json && python check_diagnostics.py --max-n 8000 --output diagnostics_replay.json)
python verify_package.py
