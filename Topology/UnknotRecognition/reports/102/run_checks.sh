#!/bin/sh
set -eu
cd "$(dirname "$0")"
python -m unittest discover -s tests -v
python scripts/audit.py
