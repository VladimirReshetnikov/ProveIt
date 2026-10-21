#!/usr/bin/env python3
"""Deterministically typeset every dense transition. No machine modification."""
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
table = {}
for line in (ROOT / 'machine/st215.tm').read_text().splitlines():
    if not line or line.startswith('#'):
        continue
    q, b, w, d, z = line.split()
    table[int(q), int(b)] = f'{w},{d},{z}'
assert len(table) == 430 and {q for q, b in table} == set(range(215))
lines = [r'\begingroup\small\ttfamily',
         r'\setlength{\tabcolsep}{9pt}',
         r'\begin{longtable}{rll@{\hspace{12mm}}rll}',
         r'\toprule',
         r'q & read 0 & read 1 & q & read 0 & read 1\\\midrule',
         r'\endfirsthead', r'\toprule',
         r'q & read 0 & read 1 & q & read 0 & read 1\\\midrule',
         r'\endhead', r'\bottomrule\endfoot']
for q in range(108):
    left = f'{q} & {table[q, 0]} & {table[q, 1]}'
    j = q + 108
    right = f'{j} & {table[j, 0]} & {table[j, 1]}' if j < 215 else ' & & '
    lines.append(left + ' & ' + right + r'\\')
lines.extend([r'\end{longtable}', r'\endgroup'])
(ROOT / 'appendices/transition_table.tex').write_text('\n'.join(lines) + '\n')
