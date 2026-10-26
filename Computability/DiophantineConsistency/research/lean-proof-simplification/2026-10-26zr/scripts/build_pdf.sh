#!/bin/sh
set -eu
task_root=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)
cd "$task_root"
latexmk -pdf -interaction=nonstopmode -halt-on-error report.tex
