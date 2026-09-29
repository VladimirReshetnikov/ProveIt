"""Build the article; optionally rerun all finite verification suites."""
from pathlib import Path
import argparse
import shutil
import subprocess
import sys

ROOT = Path(__file__).resolve().parent

def run(command: list[str]) -> None:
    subprocess.run(command, cwd=ROOT, check=True)

def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--verify', action='store_true')
    args = parser.parse_args()
    try:
        if args.verify:
            run([sys.executable, 'code/verify.py'])
            run([sys.executable, 'code/check_local_ranks.py'])
        out = ROOT / '_build'
        out.mkdir(exist_ok=True)
        if shutil.which('latexmk'):
            run(['latexmk', '-pdf', '-interaction=nonstopmode', '-halt-on-error',
                 '-outdir=_build', 'article.tex'])
        elif shutil.which('pdflatex'):
            for _ in range(3):
                run(['pdflatex', '-interaction=nonstopmode', '-halt-on-error',
                     '-output-directory=_build', 'article.tex'])
        else:
            raise RuntimeError('Install TeX Live with pdfLaTeX and the packages in article.tex')
        shutil.copy2(out / 'article.pdf', ROOT / 'article.pdf')
        print('Built', ROOT / 'article.pdf')
    except (subprocess.CalledProcessError, OSError, RuntimeError) as error:
        print(f'Build failed: {error}', file=sys.stderr)
        raise SystemExit(1) from error

if __name__ == '__main__':
    main()
