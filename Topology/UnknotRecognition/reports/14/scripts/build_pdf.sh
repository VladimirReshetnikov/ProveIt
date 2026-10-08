#!/bin/sh
set -eu
package_dir=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)
cd "$package_dir/paper"
latexmk -pdf -interaction=nonstopmode -halt-on-error -file-line-error unknot_continuation_quotients.tex
