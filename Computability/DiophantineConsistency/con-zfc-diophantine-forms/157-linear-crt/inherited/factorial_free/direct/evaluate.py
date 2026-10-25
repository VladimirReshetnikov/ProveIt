#!/usr/bin/env python3
"""Evaluate the selected fixed quartic at an explicitly supplied integer tuple."""
from pathlib import Path
import argparse,json
ROOT=Path(__file__).resolve().parent
def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('point',type=Path,help='JSON array of 242 integers (241 for the companion)')
    p.add_argument('--companion',action='store_true');a=p.parse_args();n=241 if a.companion else 242
    eq=json.loads((ROOT/f'factorial_free_affine{n}_balanced/equation.json').read_text());xs=json.loads(a.point.read_text())
    if not isinstance(xs,list)or len(xs)!=n or any(type(v)is not int for v in xs):raise ValueError('Expected exactly '+str(n)+' integers')
    values=[]
    for row in eq['residuals']:
        total=0
        for c,mon in row['terms']:
            t=c
            for i in mon:t*=xs[i]
            total+=t
        values.append(total)
    result=sum(v*v for v in values)
    print(json.dumps({'value':result,'is_zero':result==0,'nonzero_residuals':sum(v!=0 for v in values),'variables':n}))
if __name__=='__main__':main()
