#!/usr/bin/env python3
"""Render both complete, literal dense matrices into a LaTeX appendix."""
from pathlib import Path
import hashlib

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
FAMILIES = ('PA194AX11GH', 'PA194AX11GHS')

def read(family):
    path = ROOT / 'machines' / family / 'machine.tm'
    rows = {}
    for line in path.read_text().splitlines():
        q, b, w, d, n = line.split()
        key = int(q), int(b)
        if key in rows or d not in ('L', 'R'):
            raise ValueError(line)
        rows[key] = w + d + ('H' if int(n) == 194 else n)
    if set(rows) != {(q, b) for q in range(194) for b in (0, 1)}:
        raise ValueError('Incomplete table')
    return rows, hashlib.sha256(path.read_bytes()).hexdigest()

data = [read(f) for f in FAMILIES]
lines = [r'\section{Complete literal transition tables}',
         r'\label{app:literal-tables}',
         r'Both machines start in control 0 with an all-zero tape and head at position 0.',
         r'Working controls are $0,\ldots,193$; $H$ denotes terminal control 194.',
         r'An entry $wDq$ means write bit $w$, move $D\in\{L,R\}$, and enter $q$.',
         r'These are all 388 transitions of each machine, printed from the delivered byte files.',
         r'\begingroup\small\renewcommand{\arraystretch}{1.08}',
         r'\begin{longtable}{rcccc}',
         r'\caption{The two complete dense binary matrices.}\label{tab:complete-matrices}\\',
         r'\toprule & \multicolumn{2}{c}{PA194AX11GH} & \multicolumn{2}{c}{PA194AX11GHS}\\',
         r'Control & Read 0 & Read 1 & Read 0 & Read 1\\\midrule\endfirsthead',
         r'\multicolumn{5}{l}{\emph{Table \thetable{} continued}}\\',
         r'\toprule & \multicolumn{2}{c}{PA194AX11GH} & \multicolumn{2}{c}{PA194AX11GHS}\\',
         r'Control & Read 0 & Read 1 & Read 0 & Read 1\\\midrule\endhead',
         r'\bottomrule\endfoot']
for q in range(194):
    entries = [r'\texttt{' + table[q, b] + '}' for table, _ in data for b in (0, 1)]
    lines.append(str(q) + ' & ' + ' & '.join(entries) + r' \\')
lines += [r'\end{longtable}\endgroup',
          '% Input hashes: ' + ', '.join(f + '=' + h for f, (_, h) in zip(FAMILIES, data))]
(HERE / 'transition_tables.tex').write_text('\n'.join(lines) + '\n')
print('Rendered both complete matrices: 194 rows, 776 transition entries.')
