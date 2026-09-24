#!/usr/bin/env bash
# Regenerate checks and the article. Requires Python 3.10+ and a TeX installation.
set -euo pipefail
cd -- "$(dirname -- "${BASH_SOURCE[0]}")"
PYTHON="${PYTHON:-python3}"
command -v "$PYTHON" >/dev/null || { echo "Missing Python executable: $PYTHON" >&2; exit 1; }
command -v pdflatex >/dev/null || { echo "pdflatex is required to compile the article." >&2; exit 1; }
"$PYTHON" verify.py > verification_output.txt
"$PYTHON" -c 'import json; r=json.load(open("verification_report.json")); print("Mathematical software checks:", r["result"])'
for pass in 1 2 3; do
  if ! pdflatex -interaction=nonstopmode -halt-on-error article.tex > "build_pass_${pass}.log"; then
    tail -n 80 "build_pass_${pass}.log" >&2
    exit 1
  fi
done
if grep -E 'Overfull|undefined references|undefined citations|destination with the same identifier' article.log; then
  echo 'PDF compiled, but the log has layout or reference issues; inspect article.log.' >&2
  exit 1
fi
printf 'Created article.pdf and refreshed the verification reports.\n'
