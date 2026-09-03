#!/bin/sh
# Run every corpus consistency audit; nonzero exit if any fails.
#
# Run this bare and read the exit status.  Do NOT pipe it through head, tee or grep to
# tidy the output: a pipeline reports the exit status of its LAST command, so a piped
# gate can never fail.  That is not hypothetical -- a real duplicate-declaration
# collision was read as a pass that way, because the visible "exit=0" belonged to head.
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
python "$D/audit_docstring_names.py" || FAIL=1
echo
echo "== register consistency =="
python "$D/audit_register.py" || FAIL=1
echo
echo "== closed-form identities =="
python "$D/check_identities.py" || FAIL=1
echo
if [ "$FAIL" = 0 ]; then echo "ALL AUDITS PASS"; else echo "AUDITS FAILED"; fi
exit $FAIL
