"""Assemble the self-contained TeX source and compile its PDF."""
from pathlib import Path
import subprocess

ROOT = Path(__file__).resolve().parent


def main():
    text = (ROOT / 'paper_main.tex').read_text()
    text = text.replace('% ORDINARY_BRIDGE_INSERT',
                        (ROOT / 'ordinary_bridge.tex').read_text())
    text = text.replace('% VALIDATION_INSERT',
                        (ROOT / 'evidence' / 'validation.tex').read_text())
    code = (ROOT / 'code' / 'mirror_six.py').read_text().rstrip()
    text = text.replace('% CHECKER_INSERT',
                        '\\begin{lstlisting}[language=Python]\n' + code +
                        '\n\\end{lstlisting}')
    foundations = ['scalar_predecessor.tex', 'equality_reflection.tex',
                   'primitive_recursion.tex']
    text = text.replace('% ARITHMETIC_INSERT', '\n'.join(
        (ROOT / 'reference' / name).read_text() for name in foundations))
    target = ROOT / 'ipra_mirror_core.tex'
    target.write_text(text)
    logs = ROOT / 'build'
    logs.mkdir(exist_ok=True)
    for run in (1, 2, 3):
        logfile = logs / f'latex_pass_{run}.log'
        with logfile.open('w') as out:
            result = subprocess.run([
                'pdflatex', '-interaction=nonstopmode', '-halt-on-error',
                '-file-line-error', target.name], cwd=ROOT,
                stdout=out, stderr=subprocess.STDOUT)
        if result.returncode:
            raise RuntimeError(logfile.read_text()[-8000:])
    print(ROOT / 'ipra_mirror_core.pdf')


if __name__ == '__main__':
    main()
