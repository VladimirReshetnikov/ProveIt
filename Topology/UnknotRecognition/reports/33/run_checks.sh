#!/bin/sh
set -eu
cd "$(dirname "$0")"
export PYTHONPATH=src
python -m unittest discover -s tests -v
for file in artifacts/witness_*.json; do
  python src/verify_certificate.py "$file" >/dev/null
  printf 'Verified %s\n' "$file"
done
