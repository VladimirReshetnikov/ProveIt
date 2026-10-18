#!/usr/bin/env python3
"""Generate/check the complete printed canonical transition table."""
from pathlib import Path
import argparse
import hashlib

ROOT = Path(__file__).resolve().parents[1]


def render():
    path = ROOT/'machine/machine.tm'
    assert hashlib.sha256(path.read_bytes()).hexdigest() == '91ff0ff2dfe9155548d21405615934b46784c5e3cb850bbf056682d02b203790'
    table = {}
    for line in path.read_text().splitlines():
        if not line or line.startswith('#'):
            continue
        q, bit, write, direction, target = line.split()
        key = int(q), int(bit)
        assert key not in table
        table[key] = int(write), direction, int(target)
    assert set(table) == {(q,b) for q in range(244) for b in (0,1)}
    lines = [r'\clearpage', r'\section{Complete canonical transition table}', r'\label{sec:table}',
        r'The start state is 0, the runtime dispatcher is 87, and the separate',
        r'halt state is 244. An entry $(w,d,q)$ writes $w$, moves in direction',
        r'$d\in\{L,R\}$, and enters state $q$. Both columns for every working',
        r'state are present. State 244 has no outgoing transitions.',
        r'The table below is generated directly from \path{machine/machine.tm};',
        r'{\ttfamily python3\ code/render\_table.py\ -{}-check} verifies the printed source.',
        r'\begingroup\small', r'\setlength{\tabcolsep}{4.5pt}',
        r'\begin{longtable}{rll@{\hspace{12pt}}rll@{\hspace{12pt}}rll}', r'\toprule',
        r'State & Read 0 & Read 1 & State & Read 0 & Read 1 & State & Read 0 & Read 1\\',
        r'\midrule\endfirsthead', r'\toprule',
        r'State & Read 0 & Read 1 & State & Read 0 & Read 1 & State & Read 0 & Read 1\\',
        r'\midrule\endhead', r'\midrule',
        r'\multicolumn{9}{r}{\emph{Continued on next page}}\\\endfoot',
        r'\bottomrule\endlastfoot']
    def cell(q,b):
        w, direction, target = table[q,b]
        return f'$({w},{direction},{target})$'
    printed = set()
    for first in range(82):
        columns = []
        for q in (first,first+82,first+164):
            if q < 244:
                columns += [str(q),cell(q,0),cell(q,1)]
                printed.add(q)
            else:
                columns += ['','','']
        lines.append(' & '.join(columns)+r'\\')
    assert printed == set(range(244))
    lines += [r'\end{longtable}', r'\endgroup', '']
    return '\n'.join(lines)


if __name__ == '__main__':
    if not __debug__:
        raise RuntimeError('Assertions are required; do not use Python -O.')
    assert __debug__, 'Assertions are required.'
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check',action='store_true')
    args = parser.parse_args()
    dest = ROOT/'sections/table.tex'
    data = render()
    if args.check:
        assert dest.read_text() == data, 'Printed table differs from canonical transition file.'
        print('PASS_PRINTED_244_STATE_TABLE')
    else:
        dest.write_text(data)
        print(dest)
