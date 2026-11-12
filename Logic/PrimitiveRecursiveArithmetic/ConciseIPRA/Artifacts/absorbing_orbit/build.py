"""Flatten the paper into one independently compilable LaTeX source."""
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parent


def main():
    source = (ROOT / 'paper/main_template.tex').read_text()
    source = source.replace('% INSERT_PREDECESSOR',
                            (ROOT / 'paper/predecessor51_detailed.tex').read_text())
    source = source.replace('% INSERT_DEPENDENCIES',
                            (ROOT / 'paper/predecessor51_dependencies.tex').read_text())
    checker = (ROOT / 'checker/checkers/strict632.py').read_text()
    source = source.replace('% INSERT_CHECKER',
                            '\\begin{lstlisting}[language=Python]\n' + checker
                            + '\\end{lstlisting}\n')
    names = [
        'inherited_choice_basis.tex', 'inherited_ordinary_bridge.tex',
        'scalar_predecessor.tex', 'equality_reflection.tex',
        'primitive_recursion.tex', 'inherited_arity_checker.tex',
        'context_first_audit.tex',
    ]
    foundations = '\n\n'.join((ROOT / 'reference' / name).read_text()
                               for name in names)
    source = source.replace('% INSERT_FOUNDATIONS', foundations)
    if '% INSERT_' in source:
        raise ValueError('An unexpanded paper marker remains')
    target = ROOT / 'ipra_absorbing_orbit.tex'
    target.write_text(source)
    print('Wrote standalone source:', target.name)
    if '--pdf' in sys.argv:
        subprocess.run([sys.executable, str(ROOT / 'pdf_build.py'),
                        '--tex', str(target),
                        '--output', str(ROOT / 'ipra_absorbing_orbit.pdf'),
                        '--log', str(ROOT / 'evidence/pdf_build.log')],
                       cwd=ROOT, check=True)


if __name__ == '__main__':
    main()
