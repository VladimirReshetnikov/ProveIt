"""Compile the standalone report with an installed TeX Live distribution."""
from pathlib import Path
import shutil
import subprocess
import tempfile


def main():
    root = Path(__file__).resolve().parent
    with tempfile.TemporaryDirectory(prefix='ipra-witness-') as directory:
        build = Path(directory)
        shutil.copyfile(root / 'report.tex', build / 'report.tex')
        for _ in range(3):
            result = subprocess.run(
                ['pdflatex', '-no-shell-escape', '-interaction=nonstopmode',
                 '-halt-on-error', 'report.tex'], cwd=build,
                stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
            if result.returncode:
                print(result.stdout)
                raise SystemExit(result.returncode)
        shutil.copyfile(build / 'report.pdf', root / 'report.pdf')
        (root / 'evidence' / 'latex_build.log').write_text(
            (build / 'report.log').read_text(errors='replace'))
    print('Built report.pdf')


if __name__ == '__main__':
    main()
