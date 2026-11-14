#!/usr/bin/env python3
"""Regenerate exact table/hash appendices; no machine transformation."""
from pathlib import Path
import hashlib
from check_local import read, require

ROOT = Path(__file__).resolve().parents[1]
table = read(ROOT / 'machine/u208.tm', 208, 208)
lines = [
    r'\begingroup\small',
    r'\setlength{\tabcolsep}{5pt}',
    r'\begin{longtable}{@{}rll@{\hspace{10mm}}rll@{\hspace{10mm}}rll@{}}',
    r'\toprule',
    r'$q$ & Read 0 & Read 1 & $q$ & Read 0 & Read 1 & $q$ & Read 0 & Read 1\\',
    r'\midrule\endfirsthead',
    r'\toprule',
    r'$q$ & Read 0 & Read 1 & $q$ & Read 0 & Read 1 & $q$ & Read 0 & Read 1\\',
    r'\midrule\endhead',
    r'\midrule\multicolumn{9}{r}{Continued on the next page}\\\endfoot',
    r'\bottomrule\endlastfoot',
]
emitted = set()
for index in range(70):
    cells = []
    for offset in (0, 70, 140):
        q = index + offset
        if q >= 208:
            cells += ['', '', '']
            continue
        emitted.add(q)
        cells.append(str(q))
        for bit in (0, 1):
            w, d, z = table[q, bit]
            move = 'R' if d == 1 else 'L'
            cells.append(r'$' + str(w) + r'\,' + move + r'\,' + str(z) + '$')
    lines.append(' & '.join(cells) + r'\\')
require(emitted == set(range(208)), 'Incomplete report table')
lines += [r'\end{longtable}', r'\endgroup', '']
(ROOT / 'paper/transition_table.tex').write_text('\n'.join(lines))
files = [
    ('Primary dense U208', 'machine/u208.tm'),
    ('Primary native U208', 'machine/u208.native.tm'),
    ('Exact native U209 parent', 'inputs/u209.native.tm'),
    ('Unchanged primary source', 'machine/sites.json'),
    ('Compatibility dense U208', 'machine/compatibility_variant/u208.tm'),
    ('Compatibility native U208', 'machine/compatibility_variant/u208.native.tm'),
]
lines = [
    r'All hashes in this appendix are SHA-256 of the exact file bytes.',
    r'Native tables use halt 254; both dense tables use halt 208.',
]
for label, name in files:
    digest = hashlib.sha256((ROOT / name).read_bytes()).hexdigest()
    lines += [r'\paragraph{' + label + '}', r'\path{' + name + '}',
              r'\begin{center}\small\path{' + digest + r'}\end{center}']
lines += [
    r'The complete payload manifest records sizes and hashes for all sealed files.',
    r'The PDF-only supplement and the original primary U209 and unary-theory',
    r'archives are retained byte-for-byte under \path{reference/}.',
    '',
]
(ROOT / 'paper/identities.tex').write_text('\n'.join(lines))
print('Generated full table: 208 states, 416 actions; six exact identities.')
