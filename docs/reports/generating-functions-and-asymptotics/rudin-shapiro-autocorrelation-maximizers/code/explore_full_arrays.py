#!/usr/bin/env python3
"""Explore every odd-shift correlation by the exact quarter recurrence.

Requires NumPy; this is an independent exploratory check, not the all-level
proof. The supplied direct_scan.json was generated through m=26.
An int64 array with 2**(m-1) entries is retained; memory grows exponentially.
"""
from pathlib import Path
import argparse
import json
import numpy as np

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--max-level',type=int,default=20)
    parser.add_argument('--output',type=Path,default=None)
    args=parser.parse_args()
    if not 2<=args.max_level<=26:
        parser.error('Choose a level between 2 and 26 (exponential memory use).')
    previous=np.array([1],dtype=np.int64)
    current=np.array([1,-1],dtype=np.int64)
    rows=[]
    for m in range(2,args.max_level+1):
        if m>2:
            a,b=np.split(current,2)
            following=np.concatenate((b[::-1],a[::-1]+2*previous[::-1],
                                      -a+2*previous,-b))
            previous,current=current,following
        peak=int(max(current.max(),-current.min()))
        shifts=[int(2*i+1) for i in np.flatnonzero(abs(current)==peak)]
        ell=(2**(m+1)+(-1)**m)//3
        row=dict(m=m,max=peak,shifts=shifts,ell=ell,
                 delta=[k-ell for k in shifts],ratio=[k/2**m for k in shifts])
        rows.append(row)
        print(json.dumps(row),flush=True)
    if args.output:
        args.output.parent.mkdir(parents=True,exist_ok=True)
        args.output.write_text(json.dumps(rows,indent=2)+'\n')

if __name__=='__main__':
    main()
