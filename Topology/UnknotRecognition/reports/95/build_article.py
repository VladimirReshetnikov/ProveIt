"""Build the supplied article from the package root with a normal TeX install."""

from pathlib import Path
import shutil
import subprocess


ROOT = Path(__file__).resolve().parent
ARTICLE = ROOT / 'article'
MAIN = 'saturated_bundle_cancellation.tex'


def main():
    engine = shutil.which('pdflatex')
    if not engine:
        raise SystemExit('pdflatex is required to rebuild the article')
    transcript = []
    for run in range(3):
        result = subprocess.run([engine, '-interaction=nonstopmode', '-halt-on-error', MAIN],
                                cwd=ARTICLE, text=True, capture_output=True)
        transcript.append(f'PASS {run + 1}\n' + result.stdout + result.stderr)
        (ROOT / 'data/latex_build.log').write_text('\n'.join(transcript))
        if result.returncode:
            print(result.stdout[-5000:])
            raise SystemExit(result.returncode)
    print(ARTICLE / MAIN.replace('.tex', '.pdf'))


if __name__ == '__main__':
    main()
