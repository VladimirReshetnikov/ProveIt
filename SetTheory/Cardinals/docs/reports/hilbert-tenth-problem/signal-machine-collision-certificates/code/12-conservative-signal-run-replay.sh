#!/bin/sh
# Exact standard-library replay. Do not run Python with -O: assertions matter.
set -eu
cd "$(dirname "$0")"
mkdir -p receipts data
python3 code/MORITA_15_6_audit.py > receipts/MORITA_15_6_AUDIT_RESULTS.json
python3 code/conservative_signal.py > receipts/REPLAY_RECEIPT.json
python3 code/instantiate_morita.py
python3 code/quadratic_packet.py
python3 code/initial_side_checks.py
python3 code/independent_checks.py
python3 code/pivot_scale_checks.py
cmp data/MORITA_18_SIGNAL_MACHINE.json numeric/MORITA_18_SIGNAL_MACHINE.json
python3 numeric/compile_packet.py verify > numeric/COMPACT_VERIFICATION.json
python3 numeric/test_exporter.py
python3 numeric/check_original_replays.py "$(pwd)"
printf '\nAll exact replay suites passed.\n'
