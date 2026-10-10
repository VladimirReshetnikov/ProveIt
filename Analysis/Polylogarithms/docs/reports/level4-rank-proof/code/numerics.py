#!/usr/bin/env python3
"""Independent floating-point diagnostics; these are not interval certificates."""
from __future__ import annotations
import argparse, json
from pathlib import Path
import mpmath as mp
import sympy as sp
import level4 as l
ROOT=Path(__file__).resolve().parents[1]

def eval_expression(expr):
    symbols=sorted(expr.free_symbols,key=str)
    values=[]
    for atom in symbols:
        name=str(atom)
        if name=='pi': values.append(mp.pi)
        elif name=='log2': values.append(mp.log(2))
        elif name.startswith('beta_'): values.append(mp.dirichlet(int(name[5:]),[0,1,0,-1]))
        elif name.startswith('zeta_'): values.append(mp.zeta(int(name[5:])))
        else: raise ValueError(f'unknown atom: {name}')
    return sp.lambdify(symbols,expr,'mpmath')(*values)

def direct(a,b,r,s,N):
    roots=[mp.mpc(1),mp.j,mp.mpc(-1),-mp.j]
    inner=mp.mpc(0);total=mp.mpc(0)
    for n in range(1,N+1):
        total+=roots[r*n%4]*inner/mp.mpf(n)**a
        inner+=roots[s*n%4]/mp.mpf(n)**b
    return mp.im(total)

def tail_bound(a,b,N):
    if a<=1: raise ValueError('this direct absolute-tail bound requires a > 1')
    if b==1:
        return mp.mpf(N)**(1-a)*((1+mp.log(N))/(a-1)+mp.mpf(1)/(a-1)**2)
    return mp.mpf(b)/(b-1)*mp.mpf(N)**(1-a)/(a-1)

if __name__=='__main__':
    if not __debug__:
        raise RuntimeError('Do not run diagnostics with -O: assertions are required.')
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--terms',type=int,default=4096)
    parser.add_argument('--dps',type=int,default=70)
    args=parser.parse_args()
    if args.terms<1 or args.dps<30:parser.error('terms >= 1 and dps >= 30 required')
    mp.mp.dps=args.dps
    result=[]
    for w in (4,6,8):
        for coordinate,expr in zip(l.coordinates(w),l.even_values(w)):
            a,b,r,s=coordinate
            if a<3:continue
            value=eval_expression(expr)
            partial=direct(a,b,r,s,args.terms)
            error=abs(value-partial)
            bound=tail_bound(a,b,args.terms)
            assert error < bound
            result.append(dict(coordinate=coordinate,value=mp.nstr(value,40),
                               direct_error=mp.nstr(error,8),analytic_tail_bound=mp.nstr(bound,8),
                               error_bound_ratio=mp.nstr(error/bound,8)))
    record=dict(status='PASS',scope='floating-point diagnostics only; no outward rounding',
                cases=len(result),terms=args.terms,dps=args.dps,
                max_error_bound_ratio=mp.nstr(max(mp.mpf(r['error_bound_ratio']) for r in result),8),
                results=result)
    (ROOT/'data'/'numerical_diagnostics.json').write_text(json.dumps(record,indent=2)+'\n')
    print(json.dumps({k:v for k,v in record.items() if k!='results'},indent=2))
