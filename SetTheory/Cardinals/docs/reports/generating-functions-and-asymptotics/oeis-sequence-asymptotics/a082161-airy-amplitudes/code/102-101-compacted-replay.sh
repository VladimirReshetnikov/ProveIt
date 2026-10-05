#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
python checks/verify_compacted.py
python -O checks/verify_compacted.py
python checks/verify_compacted.py --negative
python -O checks/verify_compacted.py --negative
(cd checks/formal && python verify.py && python -O verify.py && python negative_tests.py && python -O negative_tests.py)
