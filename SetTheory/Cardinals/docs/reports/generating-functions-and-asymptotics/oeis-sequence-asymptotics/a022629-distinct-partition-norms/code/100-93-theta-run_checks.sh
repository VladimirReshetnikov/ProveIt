#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
python3 checks/check_identities.py
python3 checks/diagnostics/verify_summary.py
