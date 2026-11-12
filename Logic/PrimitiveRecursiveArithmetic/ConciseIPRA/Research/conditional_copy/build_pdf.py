"""Compile the standalone paper in a temporary directory, without shell escape."""
from pathlib import Path
import shutil
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parent
STEM = 'ipra_conditional_copy'


def main():
    command = shutil.which('pdflatex')
    if command is None:
        raise SystemExit('pdflatex is required to rebuild the paper.')
    with tempfile.TemporaryDirectory(prefix='ipra_conditional_copy_') as temporary:
        folder = Path(temporary)
        shutil.copy2(ROOT / (STEM + '.tex'), folder)
        for _ in range(3):
            run = subprocess.run([command, '-interaction=nonstopmode',
                                  '-halt-on-error', '-no-shell-escape', STEM + '.tex'],
                                 cwd=folder, capture_output=True, text=True)
            if run.returncode:
                print(run.stdout[-12000:])
                raise SystemExit(run.returncode)
        log = (folder / (STEM + '.log')).read_text(errors='replace')
        warnings = [line for line in log.splitlines()
                    if 'Warning' in line or 'Overfull' in line or 'Underfull' in line]
        shutil.copy2(folder / (STEM + '.pdf'), ROOT / (STEM + '.pdf'))
        (ROOT / 'evidence' / 'pdf_build.txt').write_text(
            'pdflatex, three passes, shell escape disabled.\n' +
            '\n'.join(warnings) + '\n')
        print('Built', STEM + '.pdf')
        for line in warnings:
            print(line)


if __name__ == '__main__':
    main()
