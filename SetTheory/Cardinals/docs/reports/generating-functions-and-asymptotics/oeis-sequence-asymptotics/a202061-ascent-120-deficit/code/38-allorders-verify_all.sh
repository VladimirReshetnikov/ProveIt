#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
if [[ -f SHA256SUMS ]]; then python check_manifest.py; fi
printf '\n== Pinned unchanged dependency and reviewed sources ==\n'
python checks/check_dependencies.py
python checks/check_proof_sources.py
printf '\n== Universal recurrence through P4 ==\n'
python checks/generate_action_polynomials.py 4
printf '\n== Separate direct substitution through P2 ==\n'
python checks/verify_action_coefficients.py
printf '\n== Inverse scaling and hierarchy identities ==\n'
python checks/verify_inverse_scaling.py
python checks/check_hierarchy.py
printf '\n== Independent analytic-audit checks ==\n'
python audit/independent_checks.py
printf '\n== Independent direct substitution through P4 ==\n'
python audit/verify_p3_p4_direct.py
printf '\n== Complete unchanged third-order verification ==\n'
(cd dependency/third-order && bash verify_all.sh)
printf '\nPASS: all finite-order package diagnostics\n'
