#!/usr/bin/env python3
"""Construct the (14,24) identity and verify the bounded-size inverse formula."""
from __future__ import annotations
import json
import math
from pathlib import Path
import sympy as sp
from verify_gap_ten_independent import source_matrix

HERE=Path(__file__).resolve().parent
M=5

def exact_fundamental_and_green(b):
    nmax=b+M
    beta=[sp.S.Zero]+[2*abs(sp.bernoulli(2*k))/sp.factorial(2*k)
                      for k in range(1,nmax+1)]
    aa=[0]*(nmax+1)
    rr=sp.zeros(nmax+1,M)
    gg=sp.zeros(nmax+1,b)
    for j in range(M):rr[j+1,j]=1
    for n in range(M+1,nmax+1):
        aa[n]=math.prod(range(2*n-2*M+1,2*n+1))
        bb=math.prod(range(2*n-2*M,2*n))
        dn=2*(aa[n]+bb)
        for j in range(M):
            rr[n,j]=sum(beta[n-u]*(aa[u]+bb)*rr[u,j]
                        for u in range(1,n))/dn
        for j in range(b):
            gg[n,j]=((1 if n==M+j+1 else 0)+
                     sum(beta[n-u]*(aa[u]+bb)*gg[u,j]
                         for u in range(1,n)))/dn
    return rr,gg

def inverse_by_boundary(b):
    rr,gg=exact_fundamental_and_green(b)
    F=rr[b+1:b+M+1,:]
    unscaled=gg[1:b+1,:]-rr[1:b+1,:]*F.inv(method='DM')*gg[b+1:b+M+1,:]
    result=sp.zeros(b,b)
    for k in range(b):
        n=b-k
        for r in range(b):
            N=r+M+1
            factor=sp.Rational(2*(-1)**(n+N)*sp.factorial(2*n),sp.factorial(2*r+1))
            result[k,r]=factor*unscaled[n-1,r]
    return result,rr,F

def main():
    inverse_records=[]
    for b in (6,7,8,12):
        inv,rr,F=inverse_by_boundary(b)
        source=source_matrix(b)
        assert inv*source==sp.eye(b)
        inverse_records.append({'b':b,'entries_verified':b*b,'F_determinant':str(F.det())})
    b=12;p=14;q=24
    inv,rr,F=inverse_by_boundary(b)
    lam=list(inv[0,:])
    x,y=sp.symbols('x y')
    K=sum(lam[r]*y**(2*(b+r)+1) for r in range(b))
    P=sp.Poly(sp.expand(K.subs(y,x+sp.Rational(1,2))-K.subs(y,x-sp.Rational(1,2))),x)
    w=[P.nth(2*r) for r in range(q)]
    assert P.degree()==2*q-2
    assert all(P.nth(r)==0 for r in range(1,2*q-1,2))
    def c(v,h):
        return (sp.Rational(1,v-1) if h==0 else
                sp.bernoulli(2*h,sp.Rational(1,2))*sp.rf(v,2*h-1)/sp.factorial(2*h))
    u=[sum(c(p,e)*c(q,h-e) for e in range(h+1)) for h in range(M+1)]
    S=sp.Poly(sum(sum(u[e]*w[q-1-h+e] for e in range(h+1))*x**(2*M-2*h)
                  for h in range(M+1)),x)
    product=sp.expand(P.as_expr()*sum(u[h]*x**(2-p-q-2*h) for h in range(M+1)))
    assert sp.expand(sum(product.coeff(x,k)*x**k for k in range(0,2*M+1))-S.as_expr())==0
    fprev=rr[b:b+M,:].det()
    ns=b+M
    dn=2*(math.prod(range(2*ns-2*M+1,2*ns+1))+math.prod(range(2*ns-2*M,2*ns)))
    assert w[-1]==4*b*(4*b-1)*fprev/(dn*F.det())
    # Check one actual six-by-six bordered determinant, including all signs.
    _,gg=exact_fundamental_and_green(b)
    target_r=7;N=target_r+M+1;n=b
    bordered=F.row_join(gg[b+1:b+M+1,target_r:target_r+1])
    bordered=bordered.col_join(rr[n:n+1,:].row_join(gg[n:n+1,target_r:target_r+1]))
    factor=sp.Rational(2*(-1)**(n+N)*sp.factorial(2*n),sp.factorial(2*target_r+1))
    assert lam[target_r]==factor*bordered.det()/F.det()
    payload={
        'pair':[p,q],'b':b,'half_gap':M,'right_hand_side':'-1/2',
        'definition':'sum_{n>=0}(P(n+1/2)*psi^(13)(n+1)*psi^(23)(n+1)/(13!*23!)-S(n+1/2))',
        'absolute_convergence':'summand O((n+1/2)^(-2))',
        'P_degree':P.degree(),'S_degree':S.degree(),
        'P_even_coefficients':[{'power':2*r,'value':str(w[r])} for r in range(q)],
        'S_even_coefficients':[{'power':2*r,'value':str(S.nth(2*r))} for r in range(M+1)],
        'K_odd_coefficients':[{'power':2*(b+r)+1,'value':str(lam[r])} for r in range(b)],
        'P_leading_coefficient':str(w[-1]),'S_leading_coefficient':str(S.nth(2*M)),
        'inverse_green_formula_checks':inverse_records,
        'bordered_six_by_six_example_verified':True,
        'all_checks_passed':True,
    }
    (HERE/'gap_ten_14_24_example.json').write_text(json.dumps(payload,indent=2)+'\n')
    print(json.dumps({k:v for k,v in payload.items()
                     if not k.endswith('coefficients')},indent=2))

if __name__=='__main__':main()
