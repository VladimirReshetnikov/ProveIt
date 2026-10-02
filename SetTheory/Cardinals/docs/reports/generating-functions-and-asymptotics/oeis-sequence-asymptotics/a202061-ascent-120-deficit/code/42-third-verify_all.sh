#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
if [[ -f SHA256SUMS ]]; then python check_manifest.py; fi
printf '\n== Pinned approved dependency ==\n'
python checks/check_dependencies.py
printf '\n== Independent proof source identities ==\n'
python checks/check_proof_sources.py
printf '\n== New exact algebra and scale diagnostics ==\n'
python checks/third_order_checks.py
printf '\n== Independent amplitude and constant certificate ==\n'
python audit/check_constants.py
printf '\n== Unchanged second-order verification ==\n'
(cd dependency/second-order && bash verify_all.sh)
printf '\nPASS: all third-order package diagnostics\n'
