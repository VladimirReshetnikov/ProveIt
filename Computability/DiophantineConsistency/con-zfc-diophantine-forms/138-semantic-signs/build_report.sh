#!/usr/bin/env bash
set -euo pipefail
packet_root=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
requested_output=${1:-"$PWD/rebuilt-report.pdf"}
if [[ "$requested_output" != /* ]]; then
    requested_output="$PWD/$requested_output"
fi
python3 -B "$packet_root/report/generate_tables.py" --check
report_build_dir=$(mktemp -d "${TMPDIR:-/tmp}/conzfc-report.XXXXXXXX")
trap 'rm -rf -- "$report_build_dir"' EXIT
cp "$packet_root"/report/*.tex "$report_build_dir/"
(
    cd "$report_build_dir"
    for pass in 1 2 3; do
        if ! pdflatex -interaction=nonstopmode -halt-on-error report.tex >build.stdout 2>&1; then
            cat build.stdout >&2
            exit 1
        fi
    done
    if grep -Eq 'Overfull \\hbox|Overfull \\vbox|undefined references|Reference .* undefined' report.log; then
        cat report.log >&2
        exit 1
    fi
)
mkdir -p -- "$(dirname -- "$requested_output")"
cp "$report_build_dir/report.pdf" "$requested_output"
printf 'Built %s\n' "$requested_output"
