#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
mkdir -p qa
sha256sum -c MANIFEST.sha256 > qa/replay-manifest-before.log
expected_pdf=$(sha256sum report107.pdf | cut -d' ' -f1)
python3 checks/verify_exact.py > qa/replay-exact-normal.json
python3 -O checks/verify_exact.py > qa/replay-exact-optimized.json
python3 checks/run_checks.py > qa/replay-corruptions.log
bash build.sh > qa/replay-build.log
actual_pdf=$(sha256sum report107.pdf | cut -d' ' -f1)
if [ "$expected_pdf" != "$actual_pdf" ]; then
 printf 'FAIL: PDF byte identity differs after rebuild\n' >&2
 exit 1
fi
sha256sum -c MANIFEST.sha256 > qa/replay-manifest-after.log
printf 'PASS: manifest, exact normal/-O, 62 corruptions, and byte-identical PDF rebuild\n'
