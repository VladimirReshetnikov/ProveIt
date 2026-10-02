#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
mkdir -p results build
python3 code/enumerate_rows.py > results/exact-replay.txt
python3 code/check_algebra.py > results/algebra-replay.txt
python3 code/numerics.py > results/numerical-replay.txt
python3 code/finite_gaussian_generator.py > results/finite-generator.txt
python3 code/verify_p1_symbolic.py > results/p1-symbolic.txt
python3 code/independent_constants.py > results/independent-constants.txt
python3 code/exact_truncated_rows.py > results/truncated-replay.txt
python3 code/validate_p1.py > results/p1-diagnostics.txt
bash build_pdf.sh
printf 'Full and gall-truncated exact enumeration, symbolic P1 and finite-generator checks, independent constants, and PDF rebuild passed.\n'
