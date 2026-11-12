"""Build the complete research report with pdfLaTeX, without shell escape."""
from pathlib import Path
import shutil
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parent
SOURCE = ROOT / 'ipra_checked_presentation.tex'
engine = shutil.which('pdflatex')
if not engine:
    raise SystemExit('pdfLaTeX is required; install a TeX distribution with the packages in the preamble.')
with tempfile.TemporaryDirectory(prefix='ipra-tex-') as temporary:
    extra = []
    lookup = subprocess.run(['kpsewhich', 'pdflatex.fmt'], capture_output=True, text=True)
    if not lookup.stdout.strip():
        initialization = subprocess.run([
            'pdftex', '-ini', '-etex', '-no-shell-escape', '-interaction=nonstopmode',
            '-halt-on-error', '-jobname=pdflatex', '-progname=pdflatex',
            '-output-directory', temporary, 'pdflatex.ini'],
            cwd=ROOT, capture_output=True, text=True)
        if initialization.returncode:
            raise SystemExit(initialization.stdout[-10000:] + initialization.stderr[-2000:])
        extra = ['-fmt=' + str(Path(temporary, 'pdflatex.fmt'))]
    for _ in range(3):
        result = subprocess.run([engine, *extra, '-no-shell-escape', '-interaction=nonstopmode',
                                 '-halt-on-error', '-output-directory', temporary, SOURCE.name],
                                cwd=ROOT, capture_output=True, text=True)
        if result.returncode:
            raise SystemExit(result.stdout[-10000:] + result.stderr[-2000:])
    log = Path(temporary, SOURCE.stem + '.log').read_text(errors='replace')
    shutil.copyfile(Path(temporary, SOURCE.stem + '.pdf'), SOURCE.with_suffix('.pdf'))
    (ROOT / 'evidence/pdf_build.log').write_text(log)
    print(SOURCE.with_suffix('.pdf').name)
    problems = [line for line in log.splitlines() if any(p in line for p in
                ('Overfull', 'undefined', 'multiply defined'))]
    for problem in problems:
        print(problem)
