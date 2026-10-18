#!/usr/bin/env python3
"""Generate the exact canonical transition-table appendix from the frozen file."""
from pathlib import Path
import argparse
from rebuild_machines import ROOT, read_table


def table_tex():
    table,start=read_table(ROOT/'machine/zfc_prefix246.tm')
    assert start == 0 and len(table)==492
    lines=[r'\small',r'\setlength{\tabcolsep}{13pt}',
        r'\begin{longtable}{rcc}',
        r'\caption{Complete canonical table. Each entry is write, movement, next state.}\label{tab:complete}\\',
        r'\toprule State & Read 0 & Read 1\\\midrule',r'\endfirsthead',
        r'\multicolumn{3}{l}{\small\itshape Complete canonical table, continued}\\',
        r'\toprule State & Read 0 & Read 1\\\midrule',r'\endhead',
        r'\midrule\multicolumn{3}{r}{\small\itshape Continued on next page}\\',r'\endfoot',
        r'\bottomrule',r'\endlastfoot']
    for q in range(246):
        out=[]
        for b in (0,1):
            w,d,t=table[q,b]
            out.append(f'${w}\\,{d}\\,{t}$')
        lines.append(f'{q} & {out[0]} & {out[1]}'+r'\\')
    lines.extend([r'\end{longtable}',r'\normalsize'])
    return '\n'.join(lines)+'\n'


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--check',action='store_true')
    args=ap.parse_args()
    dest=ROOT/'machine/transition-table.tex'
    text=table_tex()
    if args.check:
        assert dest.read_text()==text
    else:
        dest.write_text(text,encoding='ascii')
    print('PASS canonical table appendix: 246 rows / 492 transitions')


if __name__=='__main__':
    main()
