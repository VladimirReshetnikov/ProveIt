"""Extract the inherited mathematical sections for the supplementary PDF.

The frozen complete source report and foundation modules remain unchanged.
Only the required contiguous mathematical section is copied to sections/.
"""
from pathlib import Path

ROOT = Path(__file__).resolve().parent
source = (ROOT / 'reference/inherited_report.tex').read_text()
start = source.index(r'\section{The complete proposed presentation}')
end = source.index(r'\section{Standalone checkers, measurements, and tests}')
destination = ROOT / 'sections/inherited_composition.tex'
destination.write_text(
    '% Reproduced from the pinned incoming guarded_source report.\n'
    '% Historical references to a proposed or new calculus refer to that report.\n'
    + source[start:end])
print('Extracted the inherited mathematical composition.')
