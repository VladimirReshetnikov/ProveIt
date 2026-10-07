#!/bin/sh
set -eu
task_root=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)
cd "$task_root/article"
latexmk -pdf -interaction=nonstopmode -halt-on-error \
  -jobname=unknot_progress article.tex
