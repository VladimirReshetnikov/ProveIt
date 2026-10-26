#!/bin/sh
# Build without leaving TeX auxiliary files in the submission.
set -eu
TASK_ROOT=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
TASK_BUILD_DIR=$(mktemp -d "${TMPDIR:-/tmp}/conzfc-report.XXXXXXXX")
trap 'rm -rf "$TASK_BUILD_DIR"' EXIT HUP INT TERM
python3 -B "$TASK_ROOT/report/generate_inputs.py"
python3 -B "$TASK_ROOT/report/assemble.py"
for TASK_PASS in 1 2 3; do
    if ! pdflatex -interaction=nonstopmode -halt-on-error -file-line-error \
        -output-directory="$TASK_BUILD_DIR" -jobname=report \
        "$TASK_ROOT/report/report.tex" > "$TASK_BUILD_DIR/console.log" 2>&1; then
        cat "$TASK_BUILD_DIR/console.log"
        exit 1
    fi
done
cp "$TASK_BUILD_DIR/report.pdf" "$TASK_ROOT/report/report.pdf"
if [ -n "${CONZFC_TEX_LOG:-}" ]; then
    cp "$TASK_BUILD_DIR/report.log" "$CONZFC_TEX_LOG"
fi
printf '%s\n' "Built $TASK_ROOT/report/report.pdf"
