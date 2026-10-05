#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/checks"
python verify.py
python -O verify.py
python negative_tests.py
python -O negative_tests.py
