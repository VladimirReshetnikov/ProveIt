#!/usr/bin/env python3
"""Exact, standard-library-only certificate replay.

This verifies arithmetic and consistency of the supplied finite table. It
DOES NOT certify that the table enumerates polyominoes: regenerate the table
with the enumerator, whose correctness argument appears in the article.
No floats, numerical eigenvalues, optimization packages, or root finders are
used in a verification decision.
"""
from __future__ import annotations
from fractions import Fraction as Q
from pathlib import Path
import argparse, json
from functools import lru_cache
from model import NAMES, TERMS, fmap, defects, evalpoly
BASE=Path(__file__).resolve().parent.parent

def require(condition: bool, message: str) -> None:
    if not condition:
        raise ValueError(message)

@lru_cache(maxsize=256)
def log_unit_interval(q: Q, terms: int = 16) -> tuple[Q,Q]:
    """Enclose log(q) for 1 <= q <= 2 with exact rational endpoints."""
    require(Q(1)<=q<=Q(2), 'log argument outside [1,2]')
    u=(q-1)/(q+1)
    power=u; total=Q(0)
    for k in range(terms):
        total += 2*power/(2*k+1)
        power *= u*u
    remainder=2*power/((2*terms+1)*(1-u*u))
    return total,total+remainder

def log_interval(q: Q, terms: int = 16) -> tuple[Q,Q]:
    require(q>0,'log requires positivity')
    e=q.numerator.bit_length()-q.denominator.bit_length()
    w=q/(Q(2)**e)
    while w<1:
        w*=2;e-=1
    while w>=2:
        w/=2;e+=1
    lo,hi=log_unit_interval(w,terms)
    a,b=log_unit_interval(Q(2),terms)
    return (lo+e*a,hi+e*b) if e>=0 else (lo+e*b,hi+e*a)

def structural_checks() -> None:
    d=len(NAMES)
    graph=[set() for _ in NAMES]
    zero=[set() for _ in NAMES]
    active=set()
    nonlinear=False
    for i,row in enumerate(TERMS):
        for b,inds in row:
            require(b>=0 and all(0<=j<d for j in inds),'invalid monomial')
            graph[i].update(inds)
            if b==0 and len(inds)==1:zero[i].update(inds)
            if len(inds)>=2:nonlinear=True
            require(b>0 or len(inds)>0,'nonzero formal constant term')
    for _ in range(d):
        active |= {i for i,row in enumerate(TERMS)
                   if any(all(j in active for j in inds) for _,inds in row)}
    require(len(active)==d,'system is not productive')
    for start in range(d):
        seen={start}
        for _ in range(d):seen |= set().union(*(graph[j] for j in tuple(seen)))
        require(len(seen)==d,'dependency graph is not strongly connected')
    remaining=set(range(d))
    for _ in range(d):
        removable={i for i in remaining if not (zero[i]&remaining)}
        remaining-=removable
    require(not remaining,'zero-delay linear graph has a cycle')
    require(nonlinear,'nonlinearity missing')
    print('Structural checks: productive, strongly connected, nonlinear, proper.')

def check_table(data: dict) -> None:
    require(data['names']==NAMES,'coordinate order mismatch')
    a=data['polyominoes']; counts=data['counts']; n=len(a)
    require(len(counts)==17 and all(len(row)==n for row in counts),'table shape')
    require(a[0]==0 and all(row[0]==0 for row in counts),'zero-size convention')
    require(all(isinstance(x,int) and x>=0 for row in counts for x in row),'count type')
    require(all(a[k]<=counts[4][k]<=k*a[k] for k in range(1,n)),'G domination')
    # These equalities partition occurrences by occupancy of one adjacent cell.
    for k in range(1,n):
        for i,j,h in [(3,4,6),(4,2,7),(5,1,9),(8,15,13),(10,14,12)]:
            require(counts[i][k]==counts[j][k]+counts[h][k],f'linear partition n={k}')
    _,D=defects(counts,n-1)
    require(all(x>=0 for row in D for x in row),'negative recurrence defect')
    print(f'Table consistency: sizes 1..{n-1}; all defects nonnegative.')

def verify_upper(path: Path, data: dict) -> dict:
    cert=json.loads(path.read_text());N=cert['N'];zeta=Q(cert['zeta'])
    target=Q(cert['growth_upper']);den=cert['denominator']
    require(zeta>0 and zeta*target==1,'reciprocal mismatch')
    require(1<=N<len(data['polyominoes']),'prefix length')
    require(isinstance(den,int) and den>0,'denominator')
    require(len(cert['numerators'])==17,'vector length')
    v=[Q(x,den) for x in cert['numerators']]
    P,D=defects(data['counts'],N)
    pref=[evalpoly(p,zeta) for p in P];defect=[evalpoly(p,zeta) for p in D]
    image=fmap(zeta,v)
    tail=[x-y for x,y in zip(v,pref)]
    residual=[v[i]-image[i]+defect[i] for i in range(17)]
    require(min(tail)>=0,'negative tail budget')
    require(min(residual)>=0,'supersolution inequality failed')
    require(v[4]<1,'G budget is not below one')
    # Print exact lower bounds with conveniently small denominators.
    scaled=[(r*10**12).__floor__() for r in residual]
    print(f'{path.name}: lambda <= {target}; min residual >= {min(scaled)}/10^12; G={v[4]}')
    return {'file':path.name,'N':N,'growth_upper':str(target),'g':str(v[4]),
            'tail_budgets':[str(x) for x in tail],
            'residuals':[str(x) for x in residual],
            'residual_lower_numerators_1e12':scaled}

def verify_dual(path: Path) -> dict:
    cert=json.loads(path.read_text());z=Q(cert['zeta']);m=cert['weights']
    monomials=[(i,b,inds) for i,row in enumerate(TERMS) for b,inds in row]
    require(len(m)==len(monomials),'weight count')
    require(all(isinstance(v,int) and v>=0 for v in m) and sum(m)>0,'weights')
    r=[0]*17; incoming=[0]*17
    for w,(i,b,inds) in zip(m,monomials):
        r[i]+=w
        for j in inds:incoming[j]+=w
    require(incoming==r,'monomial balance failure')
    require(r==cert['row_sums'],'row sums mismatch')
    require(z>0 and z*Q(cert['growth_lower'])==1,'reciprocal mismatch')
    lo=Q(0);hi=Q(0)
    for w,(i,b,inds) in zip(m,monomials):
        if w:
            a,c=log_interval(z**b*Q(r[i],w),16)
            scale=10**18
            lo+=w*Q((a*scale).__floor__(),scale)
            hi+=w*Q((c*scale).__ceil__(),scale)
    require(lo>1,'dual logarithm is not greater than one')
    require(hi<Q(1001,1000),'dual log diagnostic upper bound failed')
    print(f'Dual: 53 monomials; total weight={sum(m)}; 1 < log(C) < 1001/1000.')
    print(f'Original recurrence growth >= {cert["growth_lower"]}, NOT a lower bound on lambda.')
    return {'file':path.name,'growth_lower':cert['growth_lower'],
            'exact_log_lower':str(lo),'exact_log_upper':str(hi),
            'simple_log_lower':'1','simple_log_upper':'1001/1000',
            'balance':incoming,'total_weight':sum(m)}

def main() -> None:
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--report',type=Path,default=None)
    args=parser.parse_args()
    structural_checks()
    data=json.loads((BASE/'data/profiles.json').read_text());check_table(data)
    reports=[verify_upper(p,data) for p in sorted((BASE/'data').glob('upper_N*.json'), key=lambda p: int(p.stem[7:]))]
    dual=verify_dual(BASE/'data/dual_original.json')
    # Replays the repository's previous certificate without a defect correction.
    old=[3482045,4310668,5751028,16014774,9499305,7394875,6515468,3748277,
         2390936,3084206,2902315,5050537,1238300,1015088,1664015,1375847,1132149]
    v=[Q(n,10**7) for n in old]
    require(all(x>=y for x,y in zip(v,fmap(Q(2000,9047),v))),'old certificate')
    print('Original upper certificate 4.5235: replayed exactly.')
    if args.report:
        output={'upper':reports,'dual':dual,'old_upper':'9047/2000',
                'arithmetic':'Python arbitrary-precision integers and Fraction only'}
        args.report.write_text(json.dumps(output,indent=2)+'\n')
    print('ALL ARITHMETIC CHECKS PASSED.')

if __name__=='__main__':main()
