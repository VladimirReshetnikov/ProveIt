#!/usr/bin/env bash
set -euo pipefail
rotation_package_dir="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"
cd "$rotation_package_dir"
mkdir -p build/texruntime
rotation_tex_runtime="$rotation_package_dir/build/texruntime"

# Normal TeX installations already provide these generated resources.
# This fallback supports installations containing packages but no format/map.
if ! kpsewhich pdflatex.fmt >/dev/null 2>&1; then
  pdftex -ini -etex -jobname=pdflatex -progname=pdflatex \
    -output-directory="$rotation_tex_runtime" pdflatex.ini \
    > "$rotation_tex_runtime/format-build.log"
  export TEXFORMATS="$rotation_tex_runtime:${TEXFORMATS:-}"
fi
if ! kpsewhich pdftex.map >/dev/null 2>&1; then
  python3 - "$rotation_tex_runtime" <<'PY'
from pathlib import Path
import subprocess
import sys
maps = []
for name in ('lm.map', 'cm.map', 'symbols.map', 'latxfont.map'):
    found = subprocess.run(['kpsewhich', name], text=True,
                           capture_output=True, check=True).stdout.strip()
    maps.append(Path(found).read_text())
(Path(sys.argv[1]) / 'pdftex.map').write_text('\n'.join(maps))
PY
  export TEXFONTMAPS="$rotation_tex_runtime:${TEXFONTMAPS:-}"
fi

for rotation_pass in 1 2 3; do
  if ! pdflatex -interaction=nonstopmode -halt-on-error \
      -output-directory=build euler_rodrigues_ipra.tex \
      > "build/latex-pass-$rotation_pass.log"; then
    tail -n 60 "build/latex-pass-$rotation_pass.log"
    exit 1
  fi
done
cp build/euler_rodrigues_ipra.pdf euler_rodrigues_ipra.pdf
printf '%s\n' 'Built euler_rodrigues_ipra.pdf'
