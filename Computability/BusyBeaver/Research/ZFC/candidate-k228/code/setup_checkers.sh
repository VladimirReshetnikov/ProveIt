#!/bin/bash
# Copy the two placed Source 103 runtime libraries next to the adapted checker under their
# original module names (the checker imports symbolic_runtime, which imports independent_runtime).
H="$(dirname "$0")/../../../../../../SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/code"
D="${1:-$(dirname "$0")/work}"
mkdir -p "$D"
cp "$H/103-bound239-validation-symbolic_runtime.py" "$D/symbolic_runtime.py"
cp "$H/72-fold242-runtime-independent_runtime.py" "$D/independent_runtime.py"
cp "$(dirname "$0")/check_literal_runtime.py" "$(dirname "$0")/screen.py" "$(dirname "$0")/program_compare.py" "$D/"
echo "checkers in $D"
