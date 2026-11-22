#!/usr/bin/env bash
set -euo pipefail
package_dir="$(cd -- "$(dirname -- "$0")" && pwd)"
cd "$package_dir"
python3 code/run_examples.py
python3 code/validate_continuous.py
cd "$package_dir/lean"
lake build
lake env lean Audit.lean
