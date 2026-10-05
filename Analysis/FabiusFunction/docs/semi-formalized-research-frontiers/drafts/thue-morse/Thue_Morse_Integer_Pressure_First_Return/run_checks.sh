#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
for name in verify_full_envelope verify_third_reduction verify_two_pulse verify_complex_corridor verify_spiral_constants verify_second_model_crossing; do
 python -O "checks/$name.py"
done
python -O checks/outer56/verify_outer56.py
python -O checks/negative_bridge/verify_extended_two_pulse.py
python -O checks/negative_bridge/verify_fixed_bridge_rates.py
