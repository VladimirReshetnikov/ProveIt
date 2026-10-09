#!/usr/bin/env bash
set -euo pipefail
package_dir="$(cd -- "$(dirname -- "$0")" && pwd)"
cd -- "$package_dir"
python3 code/assemble_article.py
for pass in 1 2 3; do
  pdflatex -interaction=nonstopmode -halt-on-error -file-line-error polylogarithms_research.tex > build-console.log
done
python3 - <<'PY'
from pathlib import Path
import re
log = Path("polylogarithms_research.log").read_text(errors="replace")
bad = re.findall(r"^.*(?:undefined references|Citation .* undefined|Reference .* undefined|Overfull \\[hv]box).*$", log, re.MULTILINE)
if bad:
    raise SystemExit("Review LaTeX diagnostics:\n" + "\n".join(bad))
print("Built polylogarithms_research.pdf; no undefined references or overfull boxes.")
PY
