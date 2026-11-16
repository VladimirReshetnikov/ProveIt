#!/usr/bin/env bash
set -euo pipefail
ROOT="$(cd "$(dirname "$0")" && pwd)"

cd "$ROOT/code"
python3 -m unittest -v test_certificate_kernel.py
python3 certificate_kernel.py \
  "$ROOT/examples/framework_certificate.json" \
  --report "$ROOT/verification/certificate_report.json"

cd "$ROOT/paper"
python /home/oai/skills/pdfs/scripts/latex_to_pdf.py \
  ipra_embedding_framework.tex \
  -o ipra_embedding_framework.pdf

python /home/oai/skills/pdfs/scripts/pdf_inspect.py \
  "$ROOT/paper/ipra_embedding_framework.pdf" \
  > "$ROOT/verification/pdf_inspect.txt"
python /home/oai/skills/pdfs/scripts/pdf_preflight.py \
  "$ROOT/paper/ipra_embedding_framework.pdf" \
  > "$ROOT/verification/pdf_preflight.txt"

pdftotext "$ROOT/paper/ipra_embedding_framework.pdf" \
  "$ROOT/verification/pdf_text.txt"
python3 - "$ROOT/verification/pdf_text.txt" <<'PY'
from pathlib import Path
import sys
s = Path(sys.argv[1]).read_text(errors="replace")
assert "??" not in s, "unresolved reference marker found"
assert "\ufffd" not in s, "replacement character found"
assert "Finite-trace reflection" in s
assert "Repository source audit" in s
print("PDF text checks passed")
PY
