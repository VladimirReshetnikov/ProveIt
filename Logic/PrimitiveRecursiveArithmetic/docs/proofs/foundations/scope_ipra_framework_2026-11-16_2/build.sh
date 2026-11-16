#!/usr/bin/env bash
set -euo pipefail
ROOT="$(cd "$(dirname "$0")" && pwd)"
cd "$ROOT"
python3 -m unittest -v reference/test_scope_reference.py
python3 reference/scope_reference.py --pretty > examples/demo.json
cd paper
latexmk -pdf -interaction=nonstopmode -halt-on-error scope_ipra_framework.tex
if grep -E "LaTeX Warning: (Reference|Citation).*undefined|There were undefined references" scope_ipra_framework.log; then
  echo "Unresolved references remain" >&2
  exit 1
fi
if grep -E "^! |Fatal error" scope_ipra_framework.log; then
  echo "LaTeX errors detected" >&2
  exit 1
fi
