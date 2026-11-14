#!/usr/bin/env python3
"""Regenerate the complete dense transition-table appendix from delivered data."""
from pathlib import Path
import json

ROOT = Path(__file__).resolve().parents[1]

def main():
    rows = {}
    for line in (ROOT/'machine/u221.tm').read_text().splitlines():
        if not line or line.startswith('#'):
            continue
        q, bit, write, direction, target = line.split()
        rows[int(q), int(bit)] = (int(write), direction, int(target))
    mapping = json.loads((ROOT/'machine/state_map.json').read_text())
    inverse = {int(k): int(v) for k, v in mapping['dense_to_native'].items()}
    if set(rows) != {(q,b) for q in range(221) for b in (0,1)}:
        raise ValueError('wrong dense transition domain')
    lines = [r'\begingroup\small',
             r'\setlength{\tabcolsep}{13pt}',
             r'\begin{longtable}{rrcc}',
             r'\toprule Dense state & Native state & Read 0: write, move, next & Read 1: write, move, next\\',
             r'\midrule\endfirsthead',
             r'\toprule Dense state & Native state & Read 0: write, move, next & Read 1: write, move, next\\',
             r'\midrule\endhead',
             r'\midrule\multicolumn{4}{r}{\small Continued on the next page}\\\endfoot',
             r'\bottomrule\endlastfoot']
    for q in range(221):
        def action(bit):
            w,d,z = rows[q,bit]
            return f'$({w},{d},{z})$'
        lines.append(f'{q} & {inverse[q]} & {action(0)} & {action(1)}' + r'\\')
    lines.extend([r'\end{longtable}',r'\endgroup',''])
    (ROOT/'paper/transition_table.tex').write_text('\n'.join(lines))
    print('Generated 221 state rows / 442 actions from exact dense table.')

if __name__ == '__main__':
    main()
