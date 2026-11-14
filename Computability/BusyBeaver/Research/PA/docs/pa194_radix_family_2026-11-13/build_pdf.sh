#!/usr/bin/env bash
set -euo pipefail
release_dir="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"
pdf_engine="${PDFLATEX:-pdflatex}"
pdf_options=(-interaction=nonstopmode -halt-on-error)
if [[ -n "${PDFLATEX_FMT:-}" ]]; then
  pdf_options+=("-fmt=${PDFLATEX_FMT}")
fi
python3 "$release_dir/report/generate_includes.py"
for document in report/pa194_radix_family construction/generic_cons_proof calibration/radix_calibration_standalone; do
  document_dir="${document%/*}"
  document_name="${document##*/}"
  (
    cd "$release_dir/$document_dir"
    "$pdf_engine" "${pdf_options[@]}" "$document_name.tex"
    "$pdf_engine" "${pdf_options[@]}" "$document_name.tex"
  )
done
