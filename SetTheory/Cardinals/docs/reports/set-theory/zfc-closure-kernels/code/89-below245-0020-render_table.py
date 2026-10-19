#!/usr/bin/env python3
"""Render the exact canonical transition table as a three-group LaTeX table."""
from pathlib import Path
import argparse

ROOT = Path(__file__).resolve().parents[1]


def render():
    rows = {}
    for line in (ROOT / 'machine/machine.tm').read_text().splitlines():
        if line and not line.startswith('#'):
            q, b, w, d, target = line.split()
            rows[int(q), int(b)] = w + d + target
    assert len(rows) == 490 and {q for q, b in rows} == set(range(245))
    out = [
        r'\begingroup\small\ttfamily',
        r'\setlength{\tabcolsep}{5pt}',
        r'\begin{longtable}{@{}rll@{\hspace{8mm}}rll@{\hspace{8mm}}rll@{}}',
        r'\toprule',
        r'$q$ & $0$ & $1$ & $q$ & $0$ & $1$ & $q$ & $0$ & $1$\\',
        r'\midrule\endfirsthead',
        r'\toprule',
        r'$q$ & $0$ & $1$ & $q$ & $0$ & $1$ & $q$ & $0$ & $1$\\',
        r'\midrule\endhead',
        r'\bottomrule\endfoot',
    ]
    for offset in range(82):
        line = []
        for q in (offset, offset + 82, offset + 164):
            line += [str(q), rows[q, 0], rows[q, 1]] if q < 245 else ['', '', '']
        out.append(' & '.join(line) + r'\\')
    out += [r'\end{longtable}', r'\endgroup', '']
    return '\n'.join(out)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check', action='store_true')
    args = parser.parse_args()
    path = ROOT / 'machine/table.tex'
    text = render()
    if args.check:
        assert path.read_text() == text
        print('PASS: all 490 printed rows match the canonical table.')
    else:
        path.write_text(text)
        print(path)
