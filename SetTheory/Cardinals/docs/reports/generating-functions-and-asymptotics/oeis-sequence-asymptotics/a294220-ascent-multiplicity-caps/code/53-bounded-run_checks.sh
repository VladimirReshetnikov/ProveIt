#!/bin/sh
# Offline, exact checks. No packages, network, writable working directory, or
# pre-existing generated output are required. Stop on every nonzero exit.
set -eu
ROOT=$(CDPATH= cd "$(dirname "$0")" && pwd)
PYTHON=${PYTHON:-python3}
export PYTHONDONTWRITEBYTECODE=1
"$PYTHON" -c 'import sys; sys.exit(0 if sys.version_info >= (3, 9) else "Python 3.9 or newer is required")'
printf '\n=== Exact suite, normal interpreter ===\n'
"$PYTHON" -B "$ROOT/checks/bounded_exact.py"
printf '\n=== Exact suite, optimized interpreter (-O) ===\n'
"$PYTHON" -B -O "$ROOT/checks/bounded_exact.py"
printf '\n=== Fail-closed regression suite, itself under -O ===\n'
"$PYTHON" -B -O "$ROOT/checks/test_validators.py"
printf '\nPASS: complete exact verification and fail-closed regression suite\n'
