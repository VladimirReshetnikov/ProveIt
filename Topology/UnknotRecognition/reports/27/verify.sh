#!/usr/bin/env bash
set -euo pipefail
ROOT="$(cd "$(dirname "$0")" && pwd)"
cd "$ROOT"

printf '%s\n' '[1/6] Python syntax'
python -m py_compile \
  prototype/causal_search.py \
  integration/clustered_r3_snippet.py \
  experiments/exhaustive_validation.py \
  experiments/exhaustive_catalog.py \
  tests/test_causal_search.py \
  tests/test_clustered_adapter.py

printf '%s\n' '[2/6] Unit tests'
python -m unittest discover -s tests -v

work="$(mktemp -d)"
trap 'rm -rf "$work"' EXIT

printf '%s\n' '[3/6] Deterministic generated-system validation'
python experiments/exhaustive_validation.py \
  --systems 5000 \
  --sites 6 \
  --moves 9 \
  --reductions 3 \
  --depth 6 \
  --output "$work/validation.json"

printf '%s\n' '[4/6] Exhaustive three-site catalog'
python experiments/exhaustive_catalog.py \
  --depth 4 \
  --moves-per-system 3 \
  --output "$work/catalog.json"

python - "$work/validation.json" "$work/catalog.json" <<'PY'
from __future__ import annotations
import json
import sys
from pathlib import Path

validation = json.loads(Path(sys.argv[1]).read_text())
catalog = json.loads(Path(sys.argv[2]).read_text())

expected_validation = {
    "initially_reducible": 3209,
    "no_witness_within_depth": 131,
    "witnessed": 1660,
    "frontload_failures": 0,
    "normal_form_completeness_failures": 0,
    "shorter_after_frontload": 0,
    "shortest_dependency_disconnects": 0,
}
expected_catalog = {
    "instances": 608400,
    "initially_reducible": 163800,
    "no_witness_within_depth": 272632,
    "witnessed": 171968,
    "frontload_failures": 0,
    "normal_form_completeness_failures": 0,
    "shortest_dependency_disconnects": 0,
}
actual_validation = validation["random_validation"]["counts"]
actual_catalog = catalog["counts"]
if actual_validation != expected_validation:
    raise SystemExit(f"validation counts changed: {actual_validation!r}")
if actual_catalog != expected_catalog:
    raise SystemExit(f"catalog counts changed: {actual_catalog!r}")
print("deterministic counts match the release record")
PY

printf '%s\n' '[5/6] Reproducible PDF build'
(
  cd article
  rm -f report25.aux report25.log report25.out report25.toc
  ./build.sh >/dev/null
)

printf '%s\n' '[6/6] PDF preflight'
if command -v pdfinfo >/dev/null 2>&1; then
  pages="$(pdfinfo article/report25.pdf | awk -F: '/^Pages/{gsub(/[[:space:]]/, "", $2); print $2}')"
  encrypted="$(pdfinfo article/report25.pdf | awk -F: '/^Encrypted/{gsub(/^[[:space:]]+/, "", $2); print $2}')"
  test "$pages" = "29"
  case "$encrypted" in
    no|"no (print:yes copy:yes change:yes addNotes:yes algorithm:none)") ;;
    *) echo "unexpected encryption status: $encrypted" >&2; exit 1 ;;
  esac
  printf 'PDF pages=%s, encrypted=%s\n' "$pages" "$encrypted"
else
  test -s article/report25.pdf
  printf '%s\n' 'pdfinfo unavailable; verified only that the PDF exists and is nonempty'
fi

printf '%s\n' 'All bundle checks passed.'
