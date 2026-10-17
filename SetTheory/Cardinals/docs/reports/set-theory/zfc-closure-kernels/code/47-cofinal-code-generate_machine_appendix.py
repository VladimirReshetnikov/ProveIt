#!/usr/bin/env python3
"""Generate the two-page literal transition appendix from the frozen table."""
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
table = {}
for line in (ROOT / 'machines/zfc_permutation252.tm').read_text().splitlines():
    if line and not line.startswith('#'):
        q, read, write, move, target = line.split()
        table[int(q), int(read)] = write + move + ('H' if int(target) == 252 else target)
assert len(table) == 504
lines = [r'\section{Complete 252-state transition table}\label{app:table}',
         r'The tape alphabet is $\{0,1\}$, the start state is 0, and $H=252$ is',
         r'the separate halting state. The initial tape is all zero and the head',
         r'is at integer 0. An entry $wDq$ means: write $w$, move in direction',
         r'$D\in\{L,R\}$, then enter state $q$. The working-state count is 252.',
         r'This appendix is generated directly from \path{machines/zfc_permutation252.tm}.',
         r'\par\medskip']
for page in range(2):
    if page:
        lines.extend([r'\clearpage',r'\noindent\textbf{Complete transition table, continued.}',r'\par\medskip'])
    lines.extend([r'\begin{center}', r'\small\ttfamily',
                  r'\setlength{\tabcolsep}{7pt}', r'\renewcommand{\arraystretch}{1.05}',
                  r'\begin{tabular}{rll@{\hspace{0.30in}}rll@{\hspace{0.30in}}rll}',
                  r'\toprule',
                  r'$q$ & read 0 & read 1 & $q$ & read 0 & read 1 & $q$ & read 0 & read 1\\',
                  r'\midrule'])
    for row in range(42):
        cells = []
        for group in range(3):
            q = page * 126 + group * 42 + row
            cells.extend([str(q), table[q, 0], table[q, 1]])
        lines.append(' & '.join(cells) + r'\\')
    lines.extend([r'\bottomrule', r'\end{tabular}', r'\end{center}'])
(ROOT / 'sections/machine_table.tex').write_text('\n'.join(lines) + '\n')
