#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
PYTHON="${PYTHON:-python3}"
"$PYTHON" - <<'PY'
import sys,mpmath
assert sys.version_info >= (3,10), 'Python 3.10 or newer required'
assert mpmath.__version__ == '1.3.0', 'Install pinned requirements.txt first'
print('Python',sys.version.split()[0],'; mpmath',mpmath.__version__)
PY
"$PYTHON" code/verify_manifest.py SOURCE-MANIFEST.sha256
mkdir -p .replay
work=$(mktemp -d "$PWD/.replay/run-XXXXXXXX")
cp -R code data "$work/"
run() {
  printf 'Running %s\n' "$1"
  "$PYTHON" "$work/code/$1.py" > "$work/data/$2.json"
}
run check_oeis_prefixes oeis-prefix-check
run check_unitary unitary_diagnostics
run check_saddle saddle_diagnostics
run check_fixed_saddle fixed_saddle_diagnostics
run check_cutoff_precision cutoff-precision-summary
run check_inverse inverse_diagnostics
run check_offcenter offcenter_diagnostics
run check_offcenter_replay offcenter-replay-summary
run check_offcenter_inverse offcenter_inverse_diagnostics
"$PYTHON" code/compare_replay.py data "$work/data" | tee "$work/comparison.json"
pdftotext -layout unitary-partitions.pdf "$work/reference-pdf.txt"
bash build.sh
pdftotext -layout unitary-partitions.pdf "$work/rebuilt-pdf.txt"
cmp "$work/reference-pdf.txt" "$work/rebuilt-pdf.txt"
if grep -Eq 'Warning|Overfull|Underfull|^!' .build/unitary-partitions.log; then
  echo 'Typesetting warning or box defect in final build log' >&2
  exit 1
fi
printf 'Replay and PDF build passed. Results: %s\n' "$work"
