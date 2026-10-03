#!/usr/bin/env bash
# Fresh local replay; source payloads are never overwritten.
set -euo pipefail
root="$(cd "$(dirname "$0")" && pwd)"
out="${1:-$root/output/replay}"
mkdir -p "$out"
out="$(cd "$out" && pwd)"
python3 - <<'PY'
import sys, sympy, scipy, mpmath
print('Python', sys.version.split()[0])
print('SymPy',sympy.__version__,'SciPy',scipy.__version__,'mpmath',mpmath.__version__)
PY
python3 "$root/exact_blocks.py" > "$out/exact-block-checks.json"
cmp "$root/exact-block-checks.json" "$out/exact-block-checks.json"
python3 "$root/audit/verify_frozen_ternary.py" > "$out/frozen-boundary-checks.log"
python3 "$root/dfa-transfer-audit/check_transfer.py" > "$out/dfa-transfer-checks.json"
cmp "$root/dfa-transfer-audit/exact-checks.json" "$out/dfa-transfer-checks.json"
python3 "$root/formal_recursion.py" > "$out/formal-recursion-checks.json"
cmp "$root/formal-recursion-checks.json" "$out/formal-recursion-checks.json"
mkdir -p "$out/independent-recursion"
cp "$root/all-orders-audit/check_coefficients.py" "$out/independent-recursion/"
python3 "$out/independent-recursion/check_coefficients.py" > "$out/independent-recursion/run.log"
cmp "$root/all-orders-audit/coefficients.json" "$out/independent-recursion/coefficients.json"
cmp "$root/all-orders-audit/scalar-endpoint-checks.json" "$out/independent-recursion/scalar-endpoint-checks.json"
python3 "$root/check_quasimode.py" > "$out/quasimode-checks.json"
python3 "$root/inverse-audit/check_inverse.py" > "$out/inverse-checks.json"
mkdir -p "$out/report"
cp "$root/report/ternary-airy-amplitudes.tex" "$root/report/build_pdf.sh" "$out/report/"
bash "$out/report/build_pdf.sh" > "$out/pdf-build.log"
pdftotext "$out/report/ternary-airy-amplitudes.pdf" "$out/report/text.txt"
python3 - "$out" <<'PY'
import json, pathlib, sys
p=pathlib.Path(sys.argv[1])
print(json.dumps({'status':'all exact checks and clean PDF build passed','output':str(p)},indent=2))
PY
