#!/usr/bin/env bash
# Exact source checks run from disposable copies; supplied inputs stay unchanged.
set -euo pipefail
root="$(cd "$(dirname "$0")" && pwd)"
cd "$root"
if [[ -f SHA256SUMS ]]; then sha256sum -c SHA256SUMS; fi
mkdir -p output
work="$(mktemp -d "$root/output/replay-XXXXXX")"
python3 - <<'PY' | tee "$work/versions.txt"
import sys, sympy
print('Python',sys.version)
print('SymPy',sympy.__version__)
PY
run() {
  local source="$1" name="$2"
  mkdir -p "$work/$name"
  cp "$root/$source" "$work/$name/check.py"
  python3 "$work/$name/check.py" 2>&1 | tee "$work/$name/output.txt"
}
run check_exact.py critical_exact
run check_first_correction.py first_correction
run coefficients/derive_c2.py second_correction
run independent-all-orders-audit/check_independent.py independent_coefficients
run signed-extensions/check_seeds_runs.py signed_exact
run signed-extensions/independent-audit/check_independent.py independent_signed
if [[ -f cancellation/check_cancellation.py ]]; then
  mkdir -p "$work/cancellation"
  cp "$root/cancellation/check_cancellation.py" "$root/cancellation/relaxed_low_stages.py" "$work/cancellation/"
  python3 "$work/cancellation/check_cancellation.py" 2>&1 | tee "$work/cancellation/output.txt"
  run cancellation/independent-audit/check_independent.py independent_cancellation
fi
if [[ "${1:-}" == '--pdf' ]]; then "$root/report/build_pdf.sh"; fi
printf '\nAll requested checks passed. Replay output: %s\n' "$work"
