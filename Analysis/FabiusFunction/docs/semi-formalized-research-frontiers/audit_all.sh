#!/bin/sh
# Run every corpus consistency audit; nonzero exit if any fails.
D=$(dirname "$0")
FAIL=0
echo "== facade reachability =="
python "$D/audit_facade_reachability.py" || FAIL=1
echo
echo "== crosswalk names =="
python "$D/audit_crosswalk_names.py" || FAIL=1
echo
python "$D/audit_duplicate_names.py" || FAIL=1
echo
if [ "$FAIL" = 0 ]; then echo "ALL AUDITS PASS"; else echo "AUDITS FAILED"; fi
exit $FAIL
