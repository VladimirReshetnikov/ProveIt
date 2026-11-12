"""Compile the report using pdfLaTeX with shell escape disabled."""
import subprocess
from pathlib import Path

root = Path(__file__).resolve().parent
build = root / 'build'
build.mkdir(exist_ok=True)
for _ in range(3):
    r = subprocess.run(['pdflatex', '-no-shell-escape', '-interaction=nonstopmode',
                        '-halt-on-error', '-output-directory', str(build), 'report.tex'],
                       cwd=root, text=True, capture_output=True)
    if r.returncode:
        print(r.stdout[-10000:])
        raise SystemExit(r.returncode)
(root / 'report.pdf').write_bytes((build / 'report.pdf').read_bytes())
print('Built report.pdf')
