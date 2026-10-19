#!/usr/bin/env python3
"""Generate the three-group LaTeX appendix from the exact canonical machine."""
from pathlib import Path
import argparse
import hashlib

ROOT=Path(__file__).resolve().parent
EXPECTED='909f29c493e0ccc5d6a481fd7a20a9a82eb934ab2aa7df17b5ec3789255a8c08'

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path,required=True)
    args=parser.parse_args()
    raw=(ROOT/'machines/zfc_composed238.tm').read_bytes()
    if hashlib.sha256(raw).hexdigest()!=EXPECTED:
        raise ValueError('Canonical table hash mismatch')
    rows={}
    for line in raw.decode().splitlines():
        if not line or line.startswith('#'): continue
        q,b,w,d,t=line.split();key=(int(q),int(b))
        if key in rows: raise ValueError('Duplicate transition')
        rows[key]=w+d+('H' if t=='238' else t)
    if set(rows)!={(q,b) for q in range(238) for b in range(2)}:
        raise ValueError('Wrong transition domain')
    header=r'q & read0 & read1 & q & read0 & read1 & q & read0 & read1\\'
    lines=[r'\begingroup\small\ttfamily',r'\setlength{\tabcolsep}{5pt}',
           r'\begin{longtable}{rll@{\hspace{1.3em}}rll@{\hspace{1.3em}}rll}',
           r'\toprule',header,r'\midrule\endfirsthead',r'\toprule',header,
           r'\midrule\endhead',r'\bottomrule\endfoot']
    printed=[]
    for i in range(80):
        cells=[]
        for group in range(3):
            q=i+80*group
            if q<238:
                printed.append(q);cells.extend((str(q),rows[q,0],rows[q,1]))
            else: cells.extend(('','',''))
        lines.append(' & '.join(cells)+r'\\')
    if sorted(printed)!=list(range(238)): raise ValueError('Incomplete appendix')
    lines.extend((r'\end{longtable}',r'\endgroup'))
    out=args.output.resolve()
    if out==ROOT or ROOT in out.parents:
        raise ValueError('Generate outside the delivered package')
    out.parent.mkdir(parents=True,exist_ok=True)
    out.write_text('\n'.join(lines)+'\n')
    print('Exact canonical appendix generated: 238 working states, 476 transitions.')

if __name__=='__main__':main()
