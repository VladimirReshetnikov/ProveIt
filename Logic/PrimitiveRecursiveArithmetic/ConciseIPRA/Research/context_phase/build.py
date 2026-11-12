"""Build the report with pdfLaTeX; Python standard library only."""
from pathlib import Path
import shutil
import subprocess

root = Path(__file__).resolve().parent
engine = shutil.which("pdflatex")
if not engine:
    raise SystemExit("pdfLaTeX is required to rebuild the report.")
source = "ipra_context_phase.tex"
for _ in range(3):
    result = subprocess.run(
        [engine, "-interaction=nonstopmode", "-halt-on-error", source],
        cwd=root, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
    )
    (root / "evidence" / "latex_build_output.txt").write_text(result.stdout)
    if result.returncode:
        print(result.stdout[-6000:])
        raise SystemExit(result.returncode)
print(root / "ipra_context_phase.pdf")
