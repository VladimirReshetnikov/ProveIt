#!/usr/bin/env python3
"""Exact coefficient engine for shifted Stieltjes finite-part correlations.

All coefficient arithmetic uses SymPy over Q[zeta(2),zeta(3),...].
The analytic proof and finite-part convention are in article.tex.
No floating-point identity recognition or PSLQ is used.
"""
from __future__ import annotations
import argparse
import json
from functools import lru_cache
from pathlib import Path
import sympy as sp

u,v=sp.symbols('u v')

def trunc(expr: sp.Expr, degree: int) -> sp.Expr:
    """Keep terms of total degree <= degree in u,v."""
    if degree < 0:
        return sp.S.Zero
    return sp.Add(*(c*u**i*v**j for (i,j),c in sp.Poly(sp.expand(expr),u,v).terms() if i+j<=degree))

@lru_cache(None)
def quotient_kernel(degree: int) -> sp.Expr:
    if degree<0:
        raise ValueError('degree must be nonnegative')
    # log Gamma(1-u)+log Gamma(1+u+v)-log Gamma(1+v).
    d=degree+2
    loga=sp.Add(*(sp.Symbol(f'z{k}')/k*(u**k+(-1)**k*((u+v)**k-v**k)) for k in range(2,d+1)))
    power=sp.S.One
    a=sp.S.One
    for j in range(1,d//2+1):
        power=trunc(power*loga,d)
        a+=power/sp.factorial(j)
    numerator=sp.Poly(sp.expand(a-1),u,v)
    q,r=sp.div(numerator,sp.Poly(u*(u+v),u,v))
    assert r.is_zero, 'Gamma-quotient divisibility failed'
    return trunc(q.as_expr(),degree)

def swap(expr: sp.Expr) -> sp.Expr:
    return expr.xreplace({u:v,v:u})

@lru_cache(None)
def correlation(m: int,n: int) -> sp.Expr:
    """J_mn(a), with gaK=gamma_K(a), gbK=gamma_K(1-a)."""
    if min(m,n)<0:
        raise ValueError('indices must be nonnegative')
    d=m+n
    terms=dict(sp.Poly(quotient_kernel(d),u,v).terms())
    c=terms.get((m,n),sp.S.Zero)+terms.get((n,m),sp.S.Zero)
    for (i,j),coef in terms.items():
        k=d-i-j-1
        if k<0:
            continue
        scale=(-1)**k/sp.factorial(k)
        if i<=m and j<=n:
            c+=coef*scale*sp.binomial(k+1,m-i)*sp.Symbol(f'ga{k}')
        if j<=m and i<=n:
            c+=coef*scale*sp.binomial(k+1,m-j)*sp.Symbol(f'gb{k}')
    ans=sp.Symbol(f'ga{d+1}')/sp.Integer(m+1)+sp.Symbol(f'gb{d+1}')/sp.Integer(n+1)-(-1)**d*sp.factorial(m)*sp.factorial(n)*c
    return sp.expand(ans)

def lift(expr: sp.Expr) -> sp.Expr:
    """Replace gamma_j by -Q_j; replace the constant part by -B2/2."""
    gs=sorted((s for s in expr.free_symbols if str(s).startswith(('ga','gb'))),key=str)
    const=expr.subs({g:0 for g in gs})
    out=-const*sp.Symbol('B2')/2
    for g in gs:
        out-=sp.diff(expr,g)*sp.Symbol('Q'+str(g)[1:])
    return sp.expand(out)

def contact(m: int,r: int) -> sp.Expr:
    if min(m,r)<0:
        raise ValueError('indices must be nonnegative')
    x=sp.Symbol('x')
    p=sp.prod(1+x/sp.Integer(j) for j in range(1,r+1))
    return sp.expand(p).coeff(x,m+1)*(-1)**m*sp.factorial(m)

def primitive_coefficients(m: int,r: int) -> list[sp.Expr]:
    """Coefficients of zeta^[j](1-r,x), j=0..m+1, in U_m,r."""
    if m<0 or r<1:
        raise ValueError('require m>=0 and r>=1')
    h=[sp.S.One]+[sp.S.Zero]*(m+1)
    for nu in range(1,r):
        for j in range(1,m+2):
            h[j]+=h[j-1]/sp.Integer(nu)
    scale=(-1)**(m+1)*sp.factorial(m)/sp.factorial(r-1)
    return [scale*h[m+1-j]/sp.factorial(j) for j in range(m+2)]

def weight(symbol: sp.Symbol) -> int:
    name=str(symbol)
    if name.startswith('z'): return int(name[1:])
    if name.startswith(('ga','gb')): return int(name[2:])+1
    raise ValueError(name)

def exact_checks(max_total: int=6) -> dict:
    count=0
    for d in range(max_total+1):
        for m in range(d+1):
            n=d-m
            p=correlation(m,n)
            reflection={s:sp.Symbol(('gb' if str(s).startswith('ga') else 'ga')+str(s)[2:]) for s in p.free_symbols if str(s).startswith(('ga','gb'))}
            assert sp.expand(p.xreplace(reflection)-correlation(n,m))==0
            atoms=sorted(p.free_symbols,key=str)
            for powers,coef in sp.Poly(p,*atoms).terms():
                assert sum(e*weight(a) for e,a in zip(powers,atoms))==d+2
            for a in atoms:
                if str(a).startswith(('ga','gb')):
                    assert sp.degree(p,a)<=1
            gs=[a for a in atoms if str(a).startswith(('ga','gb'))]
            for a in gs:
                for b in gs:
                    assert sp.diff(p,a,b)==0
            count+=1
    assert sp.expand(correlation(0,0)-(sp.Symbol('ga1')+sp.Symbol('gb1')-2*sp.Symbol('z2')))==0
    for r in range(1,9):
        assert contact(0,r)==sp.harmonic(r)
        assert all(contact(m,r)==0 for m in range(r,r+3))
    primitive_count=0
    for r in range(2,7):
        for m in range(7):
            c=primitive_coefficients(m,r);lower=primitive_coefficients(m,r-1)
            for j in range(m+2):
                derivative=(r-1)*c[j]-(j+1)*(c[j+1] if j+1<len(c) else 0)
                assert sp.simplify(derivative-lower[j])==0
            primitive_count+=1
    return {'primitive_recurrence_checks':primitive_count,'identities':count,'maximum_total_index':max_total,'reflection':True,'weight_homogeneity':True,'linear_Stieltjes_closure':True,'contact_checks':True}

def main() -> None:
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--max-total',type=int,default=6)
    ap.add_argument('--output',type=Path,default=Path(__file__).resolve().parents[1]/'data'/'exact_identities.json')
    args=ap.parse_args()
    if not 0<=args.max_total<=10:
        ap.error('--max-total must be in 0..10')
    result={'convention':'J_mn(a)=FP integral gamma_m(x) gamma_n({x+a}) dx, 0<a<1','symbols':'gaK=gamma_K(a); gbK=gamma_K(1-a); zK=zeta(K); QaK=Q_K(a); QbK=Q_K(1-a)','checks':exact_checks(args.max_total),'identities':[],'contact_coefficients':[]}
    for d in range(args.max_total+1):
        for m in range(d+1):
            n=d-m;p=correlation(m,n)
            result['identities'].append({'m':m,'n':n,'J':str(p),'K':str(lift(p)),'J_latex':sp.latex(p)})
    for r in range(1,9):
        result['contact_coefficients'].append({'r':r,'h_r_m_values_for_m_0_through_r':[str(contact(m,r)) for m in range(r+1)]})
    args.output.parent.mkdir(parents=True,exist_ok=True)
    args.output.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result['checks'],indent=2))
    print(f'Wrote {args.output}')
if __name__=='__main__':main()
