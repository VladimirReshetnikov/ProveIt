"""Regenerate the self-contained report source from the editable sections."""
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
SECTIONS = (
    'theory/report_front.tex',
    'theory/reversal_equivalence.tex',
    'theory/interpretations.tex',
    'theory/checker_design.tex',
    'theory/results.tex',
    'reference/arithmetic/inherited_choice_basis.tex',
    'reference/arithmetic/inherited_ordinary_bridge.tex',
    'reference/arithmetic/scalar_predecessor.tex',
    'reference/arithmetic/equality_reflection.tex',
    'reference/arithmetic/primitive_recursion.tex',
    'theory/report_end.tex',
)

if __name__ == '__main__':
    source = '\n'.join((ROOT / name).read_text() for name in SECTIONS)
    source = source.replace('@@CHECKER_SOURCE@@',
                            (ROOT / 'code/checker_rev_typed.py').read_text().rstrip())
    (ROOT / 'ipra_reversal_core.tex').write_text(source)
    print('Assembled ipra_reversal_core.tex')
