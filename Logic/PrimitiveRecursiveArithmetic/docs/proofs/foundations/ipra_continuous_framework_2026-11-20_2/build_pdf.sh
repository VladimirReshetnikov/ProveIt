#!/usr/bin/env bash
set -euo pipefail
package_dir="$(cd -- "$(dirname -- "$0")" && pwd)"
cd "$package_dir/paper"
latexmk -pdf -interaction=nonstopmode -halt-on-error report.tex
