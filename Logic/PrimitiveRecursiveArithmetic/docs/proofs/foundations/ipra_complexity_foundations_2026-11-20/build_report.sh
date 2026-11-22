#!/usr/bin/env bash
set -euo pipefail
complexity_package_dir="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"
complexity_pdf_engine="${PDFLATEX:-pdflatex}"
mkdir -p "${complexity_package_dir}/build"
cd "${complexity_package_dir}/tex"
for complexity_pass in 1 2 3; do
  "${complexity_pdf_engine}" -interaction=nonstopmode -halt-on-error \
    -output-directory="${complexity_package_dir}/build" report.tex \
    > "${complexity_package_dir}/build/latex-pass-${complexity_pass}.log" 2>&1
done
cp "${complexity_package_dir}/build/report.pdf" \
  "${complexity_package_dir}/ipra_complexity_foundations.pdf"
printf '%s\n' "Compiled ipra_complexity_foundations.pdf"
