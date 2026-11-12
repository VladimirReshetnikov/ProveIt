"""Assemble the complete standalone LaTeX source from editable sections."""
from pathlib import Path

ROOT = Path(__file__).resolve().parent


def main():
    files = ['paper/front.tex', 'paper/first_instance.tex',
             'paper/normalization_bridge.tex', 'paper/implementation.tex',
             'paper/fuel.tex', 'paper/back.tex',
             'reference/inherited_choice_basis.tex',
             'reference/inherited_ordinary_bridge.tex',
             'reference/scalar_predecessor.tex',
             'reference/equality_reflection.tex',
             'reference/primitive_recursion.tex', 'paper/end.tex']
    source = '\n\n'.join((ROOT / name).read_text() for name in files)
    checker = (ROOT / 'evidence/normalized/code__checker.py').read_text()
    source = source.replace('CHECKER_LISTING_PLACEHOLDER',
                            '\\begin{lstlisting}\n' + checker + '\\end{lstlisting}')
    (ROOT / 'ipra_first_instance.tex').write_text(source)
    print('Assembled ipra_first_instance.tex')


if __name__ == '__main__':
    main()
