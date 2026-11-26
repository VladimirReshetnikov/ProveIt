#!/usr/bin/env sh
# Build the report with a normally configured local pdfLaTeX installation.
# No network access, custom system configuration, BibTeX, or shell escape needed.
set -eu

grh_script_dir=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
grh_project_dir=$(CDPATH= cd -- "$grh_script_dir/.." && pwd)
grh_build_dir="$grh_project_dir/build/pdf"

if ! command -v pdflatex >/dev/null 2>&1; then
  printf '%s\n' 'pdfLaTeX is required. Install a TeX distribution with the packages listed in README.md.' >&2
  exit 1
fi

mkdir -p "$grh_build_dir"
cd "$grh_project_dir"

for grh_pass in 1 2 3; do
  printf 'Running pdfLaTeX pass %s of 3...\n' "$grh_pass"
  if ! pdflatex -interaction=nonstopmode -halt-on-error -file-line-error \
      -no-shell-escape -output-directory="$grh_build_dir" report.tex \
      > "$grh_build_dir/pass-$grh_pass.log" 2>&1; then
    cat "$grh_build_dir/pass-$grh_pass.log" >&2
    printf 'PDF build failed on pass %s. See %s\n' \
      "$grh_pass" "$grh_build_dir/pass-$grh_pass.log" >&2
    exit 1
  fi
done

cp "$grh_build_dir/report.pdf" "$grh_project_dir/report.pdf"
printf 'Built %s\n' "$grh_project_dir/report.pdf"
printf 'Build logs: %s\n' "$grh_build_dir"
