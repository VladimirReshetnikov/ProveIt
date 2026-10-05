"""Exact all-order rare-sector coefficients; requires SymPy.

Usage: python coefficients.py --height 5 --order 2
The returned b_j normalize R_m(n) by K_m^rare (m^m/4)^n n^{-(m-2)^2/2}.
"""
from __future__ import annotations
import argparse, json
from functools import lru_cache
from math import factorial, prod
import sympy as s
from sympy.functions.combinatorial.numbers import stirling

N=s.Symbol('N')

@lru_cache(None)
def centered_conditional(a: int):
    # Polynomial in T for E[(2X-N)^a | T], X~Bin(N,T).
    out=[s.Integer(0)]*(a+1)
    for b in range(a+1):
        for k in range(b+1):
            out[k] += s.binomial(a,b)*2**b*(-N)**(a-b)*stirling(b,k,kind=2)*s.ff(N,k)
    return tuple(s.expand(v) for v in out)

@lru_cache(None)
def moments(powers: tuple[int,...], order: int):
    """Coefficients in eps=N^-1/2 of E product Y_i^powers[i]."""
    powers=tuple(sorted((a for a in powers if a),reverse=True))
    A=sum(powers)
    if A==0: return (s.Integer(1),)+(s.Integer(0),)*order
    poly=[s.Integer(1)]
    for a in powers:
        cp=centered_conditional(a)
        nxt=[s.Integer(0)]*(len(poly)+len(cp)-1)
        for i,x in enumerate(poly):
            for j,y in enumerate(cp): nxt[i+j]+=x*y
        poly=[s.expand(x) for x in nxt]
    # A common denominator for the beta moments (N)^overline{k}/(2N+1)^overline{k}.
    numerator=s.Poly(s.expand(sum(c*s.rf(N,k)*s.rf(2*N+1+k,A-k)
                                 for k,c in enumerate(poly))),N)
    denominator=s.Poly(s.rf(2*N+1,A),N)
    if numerator.is_zero: return (s.Integer(0),)*(order+1)
    power0=A-2*(numerator.degree()-denominator.degree())
    assert power0>=0, (powers,power0)
    aa=numerator.all_coeffs();bb=denominator.all_coeffs()
    ans=[s.Integer(0)]*(order+1)
    quot=[]
    for j in range(max(0,(order-power0)//2+1)):
        value=(aa[j] if j<len(aa) else 0)-sum(bb[k]*quot[j-k] for k in range(1,min(j,len(bb)-1)+1))
        quot.append(s.cancel(value/bb[0]))
        ans[power0+2*j]=quot[-1]
    return tuple(ans)


def multiply(a,b,cut):
    out=[s.Integer(0)]*(cut+1)
    for i,x in enumerate(a):
        if x==0: continue
        for j,y in enumerate(b[:cut+1-i]):
            if y!=0: out[i+j]+=x*y
    return [s.expand(p) for p in out]


def rare_coefficients(m: int, order: int):
    if m<2 or order<0: raise ValueError('Require height>=2, order>=0')
    r=m-2; cut=2*order
    if not r: return [s.Integer(1)]+[s.Integer(0)]*order
    ys=s.symbols('y:'+str(r))
    expansion=[s.Integer(1)]+[s.Integer(0)]*cut
    for y in ys:
        # 9 * (1-2eps^2-eps*y)(1+eps*y) / ((3-2eps^2+eps*y)(3-eps*y)).
        numerator={0:s.Integer(1),2:-2-y*y,3:-2*y}
        den={2:-(6+y*y)/9,3:2*y/9}
        coeff=[]
        for k in range(cut+1):
            coeff.append(s.expand(numerator.get(k,0)-sum(v*coeff[k-j] for j,v in den.items() if j<=k)))
        expansion=multiply(expansion,coeff,cut)
    delta=s.Integer(1)
    for i in range(r):
        for j in range(i+1,r):
            delta *= (ys[i]-ys[j])**2
            q=(ys[i]+ys[j])**2/4
            expansion=multiply(expansion,[q**(k//2) if k%2==0 else 0 for k in range(cut+1)],cut)
    expectation=[s.Integer(0)]*(cut+1)
    for k,pk in enumerate(expansion):
        if pk==0: continue
        terms=s.Poly(s.expand(delta*pk),*ys).terms()
        for exponents,c in terms:
            ms=moments(tuple(sorted(exponents,reverse=True)),cut-k)
            for j,v in enumerate(ms): expectation[k+j] += c*v
    normal=factorial(r)*prod(factorial(j) for j in range(r))
    expectation=[s.cancel(v/normal) for v in expectation]
    assert all(expectation[j]==0 for j in range(1,cut+1,2))
    qcoeff=expectation[::2]
    z=s.Symbol('z')
    logouter=sum(s.bernoulli(2*k)/(2*k*(2*k-1)) *
                 (s.Rational(m)**(1-2*k)-m+2-s.Rational(2)**(1-2*k))*z**(2*k-1)
                 for k in range(1,order//2+2) if 2*k-1<=order)
    outer=s.series(s.exp(logouter),z,0,order+1).removeO()
    bs=[s.expand(outer*sum(v*z**j for j,v in enumerate(qcoeff))).coeff(z,j) for j in range(order+1)]
    return [s.factor(v) for v in bs]


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--height',type=int,default=5)
    ap.add_argument('--order',type=int,default=2)
    ap.add_argument('--output')
    args=ap.parse_args()
    result={'height':args.height,'order':args.order,
            'b':[str(v) for v in rare_coefficients(args.height,args.order)]}
    text=json.dumps(result,indent=2)+'\n'
    print(text,end='')
    if args.output:
        from pathlib import Path
        Path(args.output).write_text(text)
if __name__=='__main__': main()
