"""Assemble one self-contained TeX source from the editable sections."""
from pathlib import Path

ROOT = Path(__file__).resolve().parent


def main():
    sections = ['front.tex', 'rigidity.tex', 'binder_depth.tex',
                'checker.tex', 'finite_axiom_barrier.tex', 'bibliography.tex']
    parts = [(ROOT / 'sections' / name).read_text() for name in sections]
    listing = ('\\begin{lstlisting}\n' +
               (ROOT / 'checker/checker620.py').read_text() +
               '\\end{lstlisting}')
    source = '\n\n'.join(parts).replace('@@CHECKER_LISTING@@', listing)
    for name in ['inherited_choice_basis.tex', 'inherited_ordinary_bridge.tex',
                 'scalar_predecessor.tex', 'equality_reflection.tex',
                 'primitive_recursion.tex']:
        source += '\n\\clearpage\n' + (ROOT / 'reference' / name).read_text()
    source += '\n\\end{document}\n'
    (ROOT / 'ipra_reductions.tex').write_text(source)
    print('Assembled ipra_reductions.tex')


if __name__ == '__main__':
    main()
