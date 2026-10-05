#!/usr/bin/env bash
set -euo pipefail
src=$(cd "$(dirname "$0")" && pwd)
out=${1:-$(mktemp -d "${TMPDIR:-/tmp}/vincular-sectors-replay.XXXXXX")}
mkdir -p "$out"
cp "$src/article.tex" "$src/build.sh" "$src/check_sector_coefficients.py" \
   "$src/check_sector_numerics.py" "$src/requirements.txt" "$out/"
cd "$out"
python -O check_sector_coefficients.py > symbolic.stdout
python -O check_sector_numerics.py > numerical.stdout
bash build.sh
if grep -Eq 'Overfull|LaTeX Warning:.*undefined' build/pass-2.stdout; then
  echo 'TeX layout or reference check failed' >&2
  exit 1
fi
printf 'Clean replay passed: %s\n' "$out"
