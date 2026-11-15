#!/usr/bin/env python3
"""Generate the complete transition-table appendices from the dense tables."""
from pathlib import Path
import argparse

HERE = Path(__file__).resolve().parent


def render(name):
    rows = {}
    for line in (HERE.parent/'machines'/name/'machine.tm').read_text().splitlines():
        q, b, w, d, t = line.split()
        assert (int(q), int(b)) not in rows
        rows[int(q), int(b)] = w+d+t
    assert set(rows) == {(q, b) for q in range(194) for b in (0, 1)}
    parts = [r'\clearpage'] if name == 'PA194OMF' else []
    parts += [r'\subsection{'+name+r': all 388 transitions}',
              r'\label{tab:'+name+r'}',
              r'Dense start $0$; working states $0,\ldots,193$; terminal state $194$.',
              r'An entry $wDq$ means write $w$, move in direction $D$, and enter $q$.',
              r'\begin{center}\footnotesize\ttfamily',
              r'\setlength{\tabcolsep}{6pt}',
              r'\renewcommand{\arraystretch}{0.90}',
              r'\begin{tabular}{rrr@{\hspace{12pt}}rrr@{\hspace{12pt}}rrr@{\hspace{12pt}}rrr}',
              r'\toprule',
              r'$q$&read 0&read 1&$q$&read 0&read 1&$q$&read 0&read 1&$q$&read 0&read 1\\',
              r'\midrule']
    for row in range(49):
        cols = []
        for panel in range(4):
            q = 49*panel+row
            cols += [str(q), rows[q, 0], rows[q, 1]] if q < 194 else ['', '', '']
        parts.append('&'.join(cols)+r'\\')
    parts += [r'\bottomrule', r'\end{tabular}', r'\end{center}']
    return '\n'.join(parts)+'\n'


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check', action='store_true')
    args = parser.parse_args()
    for name in ('PA194OM', 'PA194OMF'):
        path = HERE/'generated'/f'{name}_table.tex'
        text = render(name)
        if args.check:
            assert path.read_text() == text, name
        else:
            path.write_text(text)
    print('Both complete transition-table appendices match the dense machines.')
