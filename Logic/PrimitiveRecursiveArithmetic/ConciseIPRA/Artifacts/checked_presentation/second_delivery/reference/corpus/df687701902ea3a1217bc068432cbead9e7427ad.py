"""Build the report twice; keep auxiliary files outside the deliverable tree."""
from pathlib import Path
import shutil
import subprocess

ROOT = Path(__file__).resolve().parent
BUILD = ROOT.parent / 'ipra_report_build'
BUILD.mkdir(parents=True, exist_ok=True)
for run in range(2):
    result = subprocess.run(
        ['pdflatex', '-interaction=nonstopmode', '-halt-on-error',
         '-output-directory=' + str(BUILD), 'report.tex'],
        cwd=ROOT, capture_output=True, text=True)
    (BUILD / ('pass_' + str(run + 1) + '.txt')).write_text(result.stdout + result.stderr)
    if result.returncode:
        print(result.stdout[-5000:])
        raise SystemExit(result.returncode)
shutil.copy2(BUILD / 'report.pdf', ROOT / 'report.pdf')
print('Built', ROOT / 'report.pdf')
