"""Exact polynomial and rational interval primitives (Python standard library).

Every mathematical check uses integers or fractions. Decimal arithmetic is used
only by generate_certificates.py to propose root brackets, never to accept them.
"""
from __future__ import annotations
from fractions import Fraction as F
from math import comb
from itertools import product
from typing import Dict, Tuple

Poly = Dict[Tuple[int, ...], F]

def require(condition: bool, message: str) -> None:
    if not condition:
        raise ValueError(message)

def clean(p: Poly) -> Poly:
    return {k: F(v) for k,v in p.items() if v}

def add(a: Poly, b: Poly, scale: F = F(1)) -> Poly:
    out = dict(a)
    for k,v in b.items(): out[k] = out.get(k,F(0)) + scale*v
    return clean(out)

def mul(a: Poly,b: Poly) -> Poly:
    out: Poly = {}
    for ka,va in a.items():
        for kb,vb in b.items():
            key = tuple(x+y for x,y in zip(ka,kb))
            out[key] = out.get(key,F(0)) + va*vb
    return clean(out)

def power(a: Poly,n: int) -> Poly:
    require(n >= 0,'negative polynomial exponent')
    dim = len(next(iter(a)))
    out = {(0,)*dim:F(1)}
    for _ in range(n): out=mul(out,a)
    return out

P2 = clean({(3,3):8,(3,2):8,(2,3):8,(2,2):17,(2,1):8,(2,0):8,
            (1,2):9,(1,1):-24,(1,0):-15,(0,0):9})
P3 = clean({(4,5):-8,(4,4):-8,(4,3):-8,(4,2):-8,(3,5):-8,(3,4):-8,
            (3,3):16,(3,2):16,(3,1):-8,(3,0):-8,(2,3):24,(2,2):33,
            (2,1):24,(2,0):24,(1,2):9,(1,1):-32,(1,0):-23,(0,0):9})
Q4 = clean({(18,):9,(16,):27,(15,):-8,(14,):54,(13,):-24,(12,):82,
            (11,):-48,(10,):84,(9,):-56,(8,):60,(7,):-48,(6,):34,
            (5,):-24,(4,):6,(3,):-8,(2,):3,(0,):1})

def check_polynomial_identities() -> None:
    one={(0,0):F(1)}; p={(1,0):F(1)}; py2={(1,2):F(1)}
    omy={(0,0):F(1),(0,1):F(-1)}
    for n,P in [(2,P2),(3,P3)]:
        rhs=mul(omy,mul(add(one,p),add(one,py2)))
        rhs={k:9*v for k,v in rhs.items()}
        diff=add(mul(power(add(one,py2,F(-1)),n),add(one,p)),
                 mul(power(add(one,p,F(-1)),n),add(one,py2)),F(-1))
        rhs=add(rhs,diff,F(-8))
        require(mul(omy,P)==rhs,f'P{n} defining identity failed')
    def term(k:int,sign:int=-1)->Poly:return {(0,):F(1),(k,):F(sign)}
    rhs=add({k:9*v for k,v in power(term(8),3).items()},
            mul(term(3,1),power(term(6),3)),F(-8))
    require(mul(power(term(2),3),Q4)==rhs,'Q4 defining identity failed')

def restrict_box(p: Poly, index: Tuple[int,...], denominator: int) -> Poly:
    """Substitute x_j=(u_j+index_j)/denominator, exactly."""
    out: Poly={}
    for powers,c in p.items():
        for exps in product(*(range(k+1) for k in powers)):
            value=c
            for k,j,i in zip(powers,exps,index):
                value*=F(comb(k,j)*i**(k-j),denominator**k)
            out[exps]=out.get(exps,F(0))+value
    return clean(out)

def bernstein_coefficients(p: Poly, degrees: Tuple[int,...]) -> list[F]:
    vals=[]
    for index in product(*(range(d+1) for d in degrees)):
        value=F(0)
        for powers,c in p.items():
            if all(k<=i for k,i in zip(powers,index)):
                factor=c
                for k,i,d in zip(powers,index,degrees):
                    factor*=F(comb(i,k),comb(d,k))
                value+=factor
        vals.append(value)
    return vals

def polynomial_certificates() -> dict:
    output={}
    for name,p,degrees,d in [('P2',P2,(3,3),8),('P3',P3,(4,5),4),('Q4',Q4,(18,),2)]:
        boxes=[]
        for idx in product(range(d),repeat=len(degrees)):
            values=bernstein_coefficients(restrict_box(p,idx,d),degrees)
            require(min(values)>0,f'{name} nonpositive Bernstein coefficient in {idx}')
            boxes.append({'index':list(idx),'coefficients':[str(x) for x in values],
                          'minimum':str(min(values))})
        output[name]={'degrees':list(degrees),'denominator':d,'boxes':boxes,
                      'minimum':str(min(F(x['minimum']) for x in boxes))}
    return output

def euler_weights(n:int) -> list[F]:
    require(n>=1,'Euler length must be positive')
    return [F((-1)**k*sum(comb(n,j) for j in range(k+1,n+1)),2**n) for k in range(n)]

def euler_axis_interval(b: F,n:int,grid:int,roots:list[int],verify_roots:bool=True)->tuple[F,F]:
    require(b>0 and n>=2 and grid>0,'axis interval needs b>0, n>=2, grid>0')
    require(all(isinstance(r,int) and r>=0 for r in roots),'invalid root numerator')
    require(len(roots)==2*n-2,'wrong number of power brackets')
    lo=F(0);hi=F(0); Hlo=F(0);Hhi=F(0)
    weights=euler_weights(n)
    big=grid**b.denominator
    for k in range(1,n):
        for m in (2*k-1,2*k):
            r=roots[m-1]
            if verify_roots:
                np=m**b.numerator
                require(r**b.denominator*np<=big,'lower power bracket failed')
                require((r+1)**b.denominator*np>big,'upper power bracket failed')
            Hlo+=F(r,grid);Hhi+=F(r+1,grid)
        w=weights[k]
        if w>=0:lo+=w*Hlo;hi+=w*Hhi
        else:lo+=w*Hhi;hi+=w*Hlo
    # C(b)=-2g and 0<E_N-g<(9/8)2^{-N}, n>=2.
    return -2*hi,-2*lo+F(9,4*2**n)

def euler_integer(a:int,b:int,n:int)->F:
    require(a>=0 and b>=0 and n>=1,'invalid integer Euler parameters')
    h=F(0);value=F(0)
    for k,w in enumerate(euler_weights(n)):
        if k:
            h+=F(1,(2*k-1)**b)+F(1,(2*k)**b)
        value+=w*h/F((2*k+1)**a)
    return value
