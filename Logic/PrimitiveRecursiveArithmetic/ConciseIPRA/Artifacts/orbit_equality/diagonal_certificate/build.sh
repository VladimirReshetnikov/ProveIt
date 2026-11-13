#!/bin/sh
set -eu
cd "$(dirname "$0")"
python3 -B build_certificate.py
python3 -B verify_certificate.py certificate.json
python3 -B run_checks.py
