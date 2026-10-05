#!/bin/sh
set -eu
cd "$(dirname "$0")"
python3 -O checks/check_corrections.py
python3 -O checks/check_integer_roots.py
python3 -O checks/check_reconstruction.py
python3 -O checks/check_logarithmic_reversion.py
