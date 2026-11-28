#!/usr/bin/env bash
set -euo pipefail
cd -- "$(dirname -- "$0")"
python3 -S checks/spectral/four_frequency_certificate.py replay
python3 -S checks/spectral/verify_four_frequency_values.py
python3 -S checks/spectral/verify_m3_polynomial.py
python3 checks/ehrhart/check_critical_ehrhart.py --max-power 1 --output validation/ehrhart_exact_replay.json
python3 -S checks/mixtures/check_mixture_frame.py
