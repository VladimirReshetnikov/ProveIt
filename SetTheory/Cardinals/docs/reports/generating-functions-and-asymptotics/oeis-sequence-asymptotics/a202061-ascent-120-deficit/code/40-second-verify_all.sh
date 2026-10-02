#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
if [[ -f SHA256SUMS ]]; then python check_manifest.py; fi
printf '\n== Pinned proof dependencies ==\n'
python checks/check_dependencies.py
printf '\n== New deterministic checks ==\n'
python checks/second_order_checks.py
printf '\n== Independent finite-height amplitude check ==\n'
python audit/check_finite_height_amplitude.py
printf '\n== Unchanged sharp and foundation verification ==\n'
(cd dependency/sharp-deficit && bash verify_all.sh)
printf '\nPASS: all package mathematical diagnostics\n'
