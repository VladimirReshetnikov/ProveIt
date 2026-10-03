#!/bin/sh
# Python standard library only. Assertions must remain enabled.
set -eu
cd "$(dirname "$0")"
export PYTHONDONTWRITEBYTECODE=1
python3 verify_source.py
python3 build_net.py
python3 replay_and_verify.py
python3 budget-audit/audit_budget.py
python3 checks/audit.py
python3 checks/audit_generated_families.py
python3 checks/audit_padding_and_generic_peak.py
python3 two-counter/verify_source.py
python3 two-counter/build_variant.py
python3 two-reset-audit/audit_two_reset.py
python3 two-reset-audit/compare_release_net.py
python3 shared-reset-arcs/build_shared.py
python3 shared-checks/audit_shared.py
python3 shared-checks/audit_prime_macros.py
python3 checks/audit_exact_domains.py
python3 -O checks/audit_exact_domains.py
