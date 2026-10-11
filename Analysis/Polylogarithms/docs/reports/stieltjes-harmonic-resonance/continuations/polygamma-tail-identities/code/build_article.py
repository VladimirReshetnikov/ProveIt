#!/usr/bin/env python3
"""Compile the modular research article and report meaningful LaTeX diagnostics."""
from pathlib import Path
import re
import subprocess
import sys

root = Path(__file__).resolve().parents[1]
(root/'qa').mkdir(exist_ok=True)
run = subprocess.run(['latexmk', '-pdf', '-interaction=nonstopmode',
                      '-halt-on-error', 'article.tex'], cwd=root,
                     text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
(root/'qa/build_stdout.log').write_text(run.stdout)
if run.returncode:
    print(run.stdout[-6000:])
    sys.exit(run.returncode)
log = (root/'article.log').read_text(errors='replace')
for match in re.finditer(r'(?:Overfull|Underfull|LaTeX Warning|Package hyperref Warning).*?(?=\n\n|\Z)', log, re.S):
    print(match.group(0))
print(next((line for line in log.splitlines() if line.startswith('Output written')), 'Build succeeded.'))
