"""Compile the standalone report with pdfLaTeX, without shell escape."""
from pathlib import Path
import shutil
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parent
SOURCE = ROOT / 'ipra_parameter_intro.tex'


def main():
    with tempfile.TemporaryDirectory(prefix='ipra_pdf_') as directory:
        command = ['pdflatex', '-no-shell-escape', '-interaction=nonstopmode',
                   '-halt-on-error', '-output-directory', directory, str(SOURCE)]
        for _ in range(2):
            result = subprocess.run(command, cwd=ROOT, stdout=subprocess.PIPE,
                                    stderr=subprocess.STDOUT, text=True)
            if result.returncode:
                raise RuntimeError(result.stdout[-12000:])
        pdf = Path(directory) / 'ipra_parameter_intro.pdf'
        shutil.copyfile(pdf, ROOT / pdf.name)
        log = (Path(directory) / 'ipra_parameter_intro.log').read_text()
        (ROOT / 'evidence/build_log.txt').write_text(log)
        problems = [line for line in log.splitlines()
                    if 'Overfull' in line or 'undefined' in line.lower()]
        print('Built:', ROOT / pdf.name)
        print('Layout/reference warnings:', problems)


if __name__ == '__main__':
    main()
