#!/usr/bin/env bash
set -euo pipefail
ROOT="$(cd "$(dirname "$0")" && pwd)"
MODE="${1:-all}"

run_checks() {
  cd "$ROOT/code"
  python3 -m unittest -v test_topology_kernel.py
  python3 topology_kernel.py --example
  python3 topology_kernel.py ../examples/circle_carrier.json
}

build_paper() {
  cd "$ROOT/paper"
  pdflatex -interaction=nonstopmode -halt-on-error ipra_topology_framework.tex
  pdflatex -interaction=nonstopmode -halt-on-error ipra_topology_framework.tex
  pdflatex -interaction=nonstopmode -halt-on-error ipra_topology_framework.tex
  if grep -Eq 'undefined references|Citation .+ undefined|Reference .+ undefined' ipra_topology_framework.log; then
    echo 'Unresolved LaTeX reference/citation' >&2
    exit 1
  fi
}

case "$MODE" in
  checks) run_checks ;;
  paper) build_paper ;;
  all) run_checks; build_paper ;;
  *) echo "usage: $0 [checks|paper|all]" >&2; exit 2 ;;
esac
