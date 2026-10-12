#!/usr/bin/env bash
set -euo pipefail
cd -- "$(dirname -- "$0")"
latexmk -pdf -interaction=nonstopmode -halt-on-error Deferred_Forests_and_Exceptional_Incidence.tex
