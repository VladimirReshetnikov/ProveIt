#!/usr/bin/env bash
set -euo pipefail
proveit_package_dir="$(CDPATH= cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"
proveit_python="${PROVEIT_PYTHON:-python3}"
cd "$proveit_package_dir"
"$proveit_python" code/verify_coefficients.py
"$proveit_python" code/verify_symbolic.py
"$proveit_python" code/verify_endpoints.py
"$proveit_python" code/make_figures.py
bash build.sh
