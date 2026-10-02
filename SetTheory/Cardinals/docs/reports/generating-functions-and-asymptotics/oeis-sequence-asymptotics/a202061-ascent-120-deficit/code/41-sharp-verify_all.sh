#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
if [[ -f SHA256SUMS ]]; then python check_manifest.py; fi
printf '\n== Sharp kernel exact certificate ==\n'
python kernel/derive_constants.py
printf '\n== Independent sharp identities ==\n'
python audit/independent_identities.py
printf '\n== Unchanged foundation manifest ==\n'
(cd foundation && sha256sum -c SHA256SUMS)
printf '\n== Foundation author diagnostics ==\n'
(cd foundation && bash verify_all.sh)
printf '\n== Foundation independent checks ==\n'
(cd foundation && python audit/independent_checks.py && python audit/staircase_checks.py)
printf '\nPASS: all exact and finite mathematical diagnostics\n'
