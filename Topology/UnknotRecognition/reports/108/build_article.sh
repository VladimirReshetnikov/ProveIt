#!/usr/bin/env bash
set -euo pipefail
artifact_root="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"
cd "$artifact_root/article"
TZ=UTC latexmk -pdf -interaction=nonstopmode -halt-on-error nonlinear_activation_forests.tex
