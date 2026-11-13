"""Assemble a standalone LaTeX source and compile it with shell escape disabled."""
from pathlib import Path
import shutil
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parent


def assemble():
    sections = ['front', 'new_math', 'bridge', 'implementation']
    parts = [(ROOT / 'sections' / (s + '.tex')).read_text() for s in sections]
    parts.append('\\appendix\n')
    parts += [(ROOT / 'sections' / (s + '.tex')).read_text()
              for s in ['normalization', 'inherited_foundations']]
    parts.append('\\section{Complete standalone acceptance programs}\n'
                 'These listings contain all code used for unbounded acceptance. '
                 'Only Python\'s standard JSON module is imported. '
                 'The explicitly bounded variants are separately supplied and measured.\n')
    for title, name in [('Explicit discharge: the smaller checker', 'explicit'),
                        ('Deterministic discharge: the new rule', 'deterministic')]:
        parts.append('\\subsection{' + title + '}\n\\begin{lstlisting}\n'
                     + (ROOT / 'code' / ('checker_' + name + '.py')).read_text()
                     + '\\end{lstlisting}\n')
    parts.append((ROOT / 'sections' / 'end.tex').read_text())
    (ROOT / 'report.tex').write_text('\n\n'.join(parts))


def main():
    assemble()
    with tempfile.TemporaryDirectory(prefix='ipra-pdf-') as temp:
        for _ in range(3):
            result = subprocess.run(
                ['pdflatex', '-no-shell-escape', '-interaction=nonstopmode',
                 '-halt-on-error', '-output-directory=' + temp, str(ROOT / 'report.tex')],
                cwd=ROOT, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
            if result.returncode:
                print(result.stdout[-12000:])
                raise SystemExit(result.returncode)
        shutil.copyfile(Path(temp) / 'report.pdf', ROOT / 'report.pdf')
        log = (Path(temp) / 'report.log').read_text()
        (ROOT / 'evidence/latex.log').write_text(log)
        warnings = [line for line in log.splitlines()
                    if any(x in line for x in ('Warning', 'Overfull', 'Underfull', 'undefined'))]
        (ROOT / 'evidence/latex_warnings.txt').write_text('\n'.join(warnings) + '\n')
        print('\n'.join(warnings) if warnings else 'PDF compiled: no LaTeX warnings.')
    print(ROOT / 'report.pdf')


if __name__ == '__main__':
    main()
