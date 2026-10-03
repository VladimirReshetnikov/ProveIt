#!/bin/sh
set -eu
cd "$(dirname "$0")"
python3 test_expanding_shuttle.py
python3 test_binary_expanding_shuttle.py
python3 independent/audit_arithmetic.py
python3 independent/audit_binary_shuttle.py
python3 independent/check_binary_rule.py
python3 test_exact_boundaries.py
python3 -O test_exact_boundaries.py
