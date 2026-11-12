"""Compile the standalone LaTeX report; no shell escape or downloads."""
from pathlib import Path
import shutil
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parent
SOURCE = ROOT / 'ipra_evaluation_discharge.tex'


def main():
    with tempfile.TemporaryDirectory(prefix='ipra-pdf-') as work:
        work = Path(work)
        shutil.copyfile(SOURCE, work / SOURCE.name)
        for _ in range(3):
            result = subprocess.run(['pdflatex', '-no-shell-escape', '-interaction=nonstopmode',
                                     '-halt-on-error', SOURCE.name],
                                    cwd=work, text=True, capture_output=True)
            if result.returncode:
                raise RuntimeError(result.stdout[-15000:] + result.stderr)
        shutil.copyfile(work / SOURCE.with_suffix('.pdf').name, SOURCE.with_suffix('.pdf'))
        (ROOT / 'evidence/latex-build.log').write_text((work / SOURCE.with_suffix('.log').name).read_text())
    print(SOURCE.with_suffix('.pdf').name)


if __name__ == '__main__':
    main()
