#!/usr/bin/env python3
"""Generate or byte-check the complete printed canonical table."""
from pathlib import Path
import argparse
import hashlib

ROOT = Path(__file__).resolve().parents[1]
SHA = '64ddeb2c01c3e9c7feffaffaad87266a270716c9307892a0445bf869b988984d'

def rendered():
    p = ROOT / 'machine/zfc_zero_reuse242.tm'
    data = p.read_bytes()
    if hashlib.sha256(data).hexdigest() != SHA:
        raise ValueError('Canonical machine identity differs')
    rows = {}
    for line in data.decode('ascii').splitlines():
        if line and not line.startswith('#'):
            q, b, w, d, t = line.split()
            rows[int(q), int(b)] = f'{w}{d}{t}'
    if set(rows) != {(q, b) for q in range(242) for b in (0, 1)}:
        raise ValueError('Wrong complete row domain')
    heading = r'\textbf{State}&\textbf{0}&\textbf{1}&\textbf{State}&\textbf{0}&\textbf{1}&\textbf{State}&\textbf{0}&\textbf{1}\\'
    lines = [r'\begingroup\small\ttfamily', r'\setlength{\tabcolsep}{7pt}',
             r'\begin{longtable}{@{}rrr@{\qquad}rrr@{\qquad}rrr@{}}',
             r'\toprule', heading, r'\midrule\endfirsthead',
             r'\toprule', heading, r'\midrule\endhead',
             r'\bottomrule\endfoot']
    for i in range(81):
        cells = []
        for q in (i, i+81, i+162):
            cells.extend([str(q), rows[q, 0], rows[q, 1]] if q < 242 else ['', '', ''])
        lines.append('&'.join(cells) + r'\\')
    lines.extend([r'\end{longtable}', r'\endgroup', ''])
    return '\n'.join(lines)

def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--check', action='store_true')
    args = ap.parse_args()
    target = ROOT / 'paper/transition_table.tex'
    text = rendered()
    if args.check:
        if target.read_text() != text:
            raise ValueError('Printed transition table differs from the machine')
        print('PASS: complete printed transition table matches canonical machine')
    else:
        target.write_text(text)
        print(target)

if __name__ == '__main__':
    main()
