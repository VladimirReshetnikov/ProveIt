#!/usr/bin/env bash
set -euo pipefail
ROOT=$(cd "$(dirname "$0")/.." && pwd)
WORK=${1:-$(mktemp -d)}
mkdir -p "$WORK/results"
WORK=$(cd "$WORK" && pwd)
PYTHON=${PYTHON:-python3}
"$PYTHON" -c 'import sympy; assert sympy.__version__ == "1.14.0", sympy.__version__'
"$PYTHON" "$ROOT/scripts/check_operator.py" > "$WORK/results/operator.txt"
"$PYTHON" "$ROOT/scripts/check_independent.py" > "$WORK/results/independent.txt"
diff -u "$ROOT/results/operator.txt" "$WORK/results/operator.txt"
diff -u "$ROOT/results/independent.txt" "$WORK/results/independent.txt"
bash "$ROOT/scripts/build_pdf.sh" "$WORK/build"
echo "All exact checks and reference-output comparisons passed. Replay directory: $WORK"
