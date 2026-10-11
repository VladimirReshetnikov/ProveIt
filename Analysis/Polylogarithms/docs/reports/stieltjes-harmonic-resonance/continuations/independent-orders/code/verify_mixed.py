#!/usr/bin/env python3
"""Independent finite-coefficient audit of reduce_mixed.py.

Left sides are formed by direct convolution of the ORIGINAL weighted
single-polylogarithm coefficients. Right sides are evaluated by finite
nested sums from the compiler output. The checker does not reuse the
root filter, shuffle, partial-fraction, or elimination implementation.
These finite checks audit conventions; the general identity has the
analytic/algebraic proof supplied in the article.
"""
from functools import lru_cache
from pathlib import Path
import json
import time
import sympy as sp
from reduce_mixed import reduce_mixed,serialize

BASE=Path(__file__).resolve().parents[1]/'results'
BASE.mkdir(exist_ok=True)


def exact(value):
    return sp.simplify(sp.expand_complex(value))


def direct_coefficients(orders,colors,weights,N):
    colors=[sp.sympify(x,locals={'I':sp.I}) for x in colors]
    values=[sp.S.One]+[sp.S.Zero]*N
    for a,x,p in zip(orders,colors,weights):
        factor=[sp.S.Zero]*(N+1)
        for m in range(1,N//p+1):
            factor[p*m]=x**m/sp.Integer(m)**a
        new=[sp.S.Zero]*(N+1)
        for j,v in enumerate(values):
            for k in range(1,N-j+1):
                new[j+k]+=v*factor[k]
        values=[exact(v) for v in new]
    return values


@lru_cache(maxsize=30000)
def nested_tail(indices,colors,upper):
    if not indices:
        return sp.S.One
    return sum((colors[0]**m/sp.Integer(m)**indices[0]*
                nested_tail(indices[1:],colors[1:],m)
                for m in range(1,upper)),sp.S.Zero)


def nested_coefficient(term,N):
    colors=(term.alphabet[0],)+tuple(
        exact(b/a) for a,b in zip(term.alphabet,term.alphabet[1:]))
    return colors[0]**N/sp.Integer(N)**term.offset*\
        nested_tail(term.inner,colors[1:],N)


def main():
    cases=[
      ('distinct_rational',[2,1,-1],['1/2','1/3','2/3'],[1,1,1],16),
      ('confluent_printed',[1,1,-2],['1/2']*3,[1,1,1],20),
      ('several_rational_factors',[2,0,-2],['1/3','1/3','1/2'],[1,1,1],16),
      ('two_negative_orders',[1,-1,-1],['1/2','1/3','1/2'],[1,1,1],16),
      ('deeper_confluent_elimination',[2,1,-3],['1/2']*3,[1,1,1],16),
      ('depth_four',[1,1,1,-1],['1/2']*4,[1,1,1,1],14),
      ('pure_rational',[0,-1],['1/4','1/2'],[1,1],16),
      ('all_positive',[1,2],['1/2','1/3'],[1,1],16),
      ('weighted_square_roots',[1,0],['1/4','1/3'],[2,1],14),
      ('weighted_mixed',[1,1,-1],['1/4','1/3','1/2'],[2,1,1],14),
      ('weighted_gaussian_roots',[1,0],['-1','1/2'],[2,1],10),
      ('weighted_cubic_confluence',[1,0],['1/8','1/2'],[3,1],8),
      ('resonant_boundary',[1,1,-1],['1']*3,[1,1,1],16),
    ]
    result=[]
    start=time.monotonic()
    for name,orders,colors,weights,N in cases:
        begin=time.monotonic()
        reduction=reduce_mixed(orders,colors,weights)
        direct=direct_coefficients(orders,colors,weights,N)
        for n in range(1,N+1):
            got=exact(sum((c*nested_coefficient(t,n) for t,c in reduction.items()),sp.S.Zero))
            if exact(got-direct[n])!=0:
                raise ArithmeticError((name,n,direct[n],got))
        row={'name':name,'orders':orders,'colors':colors,'weights':weights,
             'coefficients_checked':N,'output_terms':len(reduction),
             'max_depth':max((t.depth for t in reduction),default=0),
             'elapsed_seconds':round(time.monotonic()-begin,4),'exact_residual':'0'}
        result.append(row)
        print(json.dumps(row),flush=True)
        if name in {'confluent_printed','weighted_mixed','weighted_cubic_confluence'}:
            (BASE/(name+'_reduction.json')).write_text(json.dumps(
                {'input':{'orders':orders,'colors':colors,'weights':weights},
                 'terms':serialize(reduction)},indent=2)+'\n')
    record={'schema':'proveit.mixed-integer-orders.coefficient-audit.v1',
            'cases':result,'total_coefficients_checked':sum(x['coefficients_checked'] for x in result),
            'all_exact':True,'elapsed_seconds':round(time.monotonic()-start,4),
            'proof_scope':'Finite independent coefficient checks; the article proves the all-order identity.'}
    (BASE/'mixed_checks.json').write_text(json.dumps(record,indent=2)+'\n')
    print(json.dumps({k:v for k,v in record.items() if k!='cases'}),flush=True)


if __name__=='__main__':
    main()
