#!/usr/bin/env python3
"""Typeset the exact dense table in four parallel column groups."""
from pathlib import Path

here = Path(__file__).resolve().parent
rows = {}
for line in (here.parent / 'artifacts/pa194_tdy.tm').read_text().splitlines():
    if not line.strip() or line.lstrip().startswith('#'):
        continue
    q, b, w, d, target = line.split()
    rows[int(q), int(b)] = f'{w}{d}{target}'
assert set(rows) == {(q, b) for q in range(194) for b in range(2)}
out = [r'\begingroup', r'\fontsize{9}{11}\selectfont',
       r'\setlength{\tabcolsep}{4pt}', r'\renewcommand{\arraystretch}{0.97}',
       r'\begin{center}', r'\begin{tabular}{@{}rll@{\qquad}rll@{\qquad}rll@{\qquad}rll@{}}',
       r'\toprule', ' & '.join(['Control & Read 0 & Read 1'] * 4) + r'\\\midrule']
for i in range(49):
    cells = []
    for block in range(4):
        q = i + 49 * block
        cells.extend([str(q), r'\texttt{' + rows[q, 0] + '}', r'\texttt{' + rows[q, 1] + '}'] if q < 194 else ['', '', ''])
    out.append(' & '.join(cells) + r'\\')
out += [r'\bottomrule', r'\end{tabular}', r'\end{center}', r'\endgroup']
(here / 'transition_table.tex').write_text('\n'.join(out) + '\n')
