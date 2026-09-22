#!/usr/bin/env python3
"""Exact finite checks for Infinitesimal Resonance and Hidden Monodromy.

Python 3.9+; standard library only. These are computational checks of finite
identities, not a formal verification of the article's infinite theorems.
Run from any directory: python code/verify.py
"""
from fractions import Fraction as F
from math import comb
from pathlib import Path
import csv
import json
import platform

CHECKS = 0

def check(condition, label):
    global CHECKS
    if not condition:
        raise AssertionError(label)
    CHECKS += 1

def pad(a, n):
    return list(a[:n]) + [F(0)] * max(0, n-len(a))

def add(a,b,n):
    a,b=pad(a,n),pad(b,n)
    return [a[k]+b[k] for k in range(n)]

def mul(a,b,n):
    a,b=pad(a,n),pad(b,n)
    return [sum((a[j]*b[k-j] for j in range(k+1)),F(0)) for k in range(n)]

def scale(a,c,n):
    return [c*x for x in pad(a,n)]

def shift(a,k,n):
    return pad([F(0)]*k+list(a),n)

def divide(a,b,n):
    a,b=pad(a,n),pad(b,n)
    if not b[0]:
        raise ZeroDivisionError('The denominator must have nonzero constant term.')
    out=[]
    for k in range(n):
        out.append((a[k]-sum((b[j]*out[k-j] for j in range(1,k+1)),F(0)))/b[0])
    return out

def lambda_power(k,n):
    assert k >= 0
    return [F(comb(k,j)) if j<=k else F(0) for j in range(n)]

def koenigs(q,mmax,order):
    n=order+1
    b=[[F(1)]+[F(0)]*order]
    for m in range(1,mmax+1):
        numerator=[F(0)]*n
        for j in range(m):
            k=m-j
            d=q*j+1
            if k>d:
                continue
            term=mul(b[j],lambda_power(d-k,n),n)
            numerator=add(numerator,scale(shift(term,k-1,n),F(comb(d,k)),n),n)
        d=q*m+1
        denominator=[F(comb(d,k+1)) if k+1<=d else F(0) for k in range(n)]
        denominator[0]-=1
        b.append(scale(divide(numerator,denominator,n),F(-1),n))
    return b

def pochhammer_coeffs(q,mmax):
    c=[F(1)]
    for m in range(1,mmax+1):
        c.append(-c[-1]*(F(1,q)+m-1)/m)
    return c

def sparse_add(a,b,c=F(1)):
    out=dict(a)
    for k,v in b.items():
        out[k]=out.get(k,F(0))+c*v
        if not out[k]:
            del out[k]
    return out

def substitution_difference(a,q,p):
    """N=A -> A(w+epsilon*(w+w**(q+1)))-A, modulo epsilon**(p+1)."""
    out={}
    for (e,d),coef in a.items():
        for k in range(1,min(d,p-e)+1):
            for j in range(k+1):
                key=(e+k,d+q*j)
                out[key]=out.get(key,F(0))+coef*comb(d,k)*comb(k,j)
    return {k:v for k,v in out.items() if v}

def log_substitution(a,q,p):
    term=dict(a)
    out={}
    for r in range(1,p+1):
        term=substitution_difference(term,q,p)
        out=sparse_add(out,term,F((-1)**(r+1),r))
    return out

def poly_mul(a,b):
    out={}
    for i,u in a.items():
        for j,v in b.items():
            out[i+j]=out.get(i+j,F(0))+u*v
    return {k:v for k,v in out.items() if v}

def poly_deriv(a):
    return {k-1:k*v for k,v in a.items() if k}

def poly_sum(*parts):
    out={}
    for c,a in parts:
        for k,v in a.items():
            out[k]=out.get(k,F(0))+c*v
    return {k:v for k,v in out.items() if v}

def main():
    root=Path(__file__).resolve().parents[1]
    data=root/'data'
    data.mkdir(exist_ok=True)
    order,mmax=8,24
    sample=[]
    for q in range(1,9):
        b=koenigs(q,mmax,order)
        c=pochhammer_coeffs(q,mmax)
        log=[F(0)]+[F((-1)**(m+1),m) for m in range(1,mmax+1)]
        cl=mul(c,log,mmax+1)
        cll=mul(cl,log,mmax+1)
        A=F(q+1,2*q)
        B=F((q+1)*(q-4),12*q)
        C=F((q+1)*(2*q+1),12*q)
        for m in range(mmax+1):
            check(b[m][0]==c[m],f'q={q}, m={m}: leading binomial coefficient')
            check(b[m][1]==A*cl[m],f'q={q}, m={m}: first logarithmic coefficient')
            h2=B*cl[m]+A*A*cll[m]/2-(C*c[m-1] if m else 0)
            check(b[m][2]==h2,f'q={q}, m={m}: second coefficient')
            n=order+2
            residual=[F(0)]*n
            for j in range(m+1):
                k=m-j
                d=q*j+1
                if k>d:
                    continue
                term=mul(b[j],lambda_power(d-k,n),n)
                residual=add(residual,scale(shift(term,k,n),F(comb(d,k)),n),n)
            residual=add(residual,scale(mul(b[m],[F(1),F(1)],n),F(-1),n),n)
            for k,r in enumerate(residual):
                check(r==0,f'q={q}, m={m}, epsilon^{k}: Schroeder residual')
            if m<=5:
                sample.append([q,m]+[str(x) for x in b[m][:5]])
        # rho=log(1+epsilon)/log(1-q*epsilon), cancelling epsilon first.
        top=[F((-1)**k,k+1) for k in range(order+1)]
        bottom=[F(-(q**(k+1)),k+1) for k in range(order+1)]
        rho=divide(top,bottom,order+1)
        check(rho[0]==F(-1,q),f'q={q}: rho constant')
        check(rho[1]==A,f'q={q}: rho first coefficient')
        check(rho[2]==B,f'q={q}: rho second coefficient')
        check(q*rho[1]==F(q+1,2),f'q={q}: nonzero monodromy obstruction')

    for q in range(1,7):
        p=6
        D=log_substitution({(0,1):F(1)},q,p)
        # Independently check log(C_g) is a derivation on monomials.
        for n in range(7):
            got=log_substitution({(0,n):F(1)},q,p)
            want={(e,d+n-1):n*c for (e,d),c in D.items()} if n else {}
            check(got==want,f'q={q}, w^{n}: logarithm derivation through epsilon^6')
        V={1:F(1),q+1:F(1)}
        Vp=poly_deriv(V)
        Vpp=poly_deriv(Vp)
        expected=[V,poly_sum((F(-1,2),poly_mul(V,Vp))),
            poly_sum((F(1,12),poly_mul(poly_mul(V,V),Vpp)),
                     (F(1,3),poly_mul(V,poly_mul(Vp,Vp))))]
        for r in range(3):
            got={d:c for (e,d),c in D.items() if e==r+1}
            check(got==expected[r],f'q={q}: modified vector field order {r}')
        # Derivative at roots a**q=-1, via polynomial reduction.
        for e in range(1,p+1):
            reduced={}
            slope0=F(0)
            for (ee,d),c in D.items():
                if ee!=e or d==0:
                    continue
                if d==1:
                    slope0+=c
                exponent=d-1
                rem=exponent%q
                val=d*c*((-1)**(exponent//q))
                reduced[rem]=reduced.get(rem,F(0))+val
            reduced={k:v for k,v in reduced.items() if v}
            check(slope0==F((-1)**(e+1),e),f'q={q}: log multiplier at 0, order {e}')
            check(reduced=={0:F(-(q**e),e)},f'q={q}: log multiplier at a, order {e}')

    with (data/'coefficients.csv').open('w',newline='',encoding='utf-8') as f:
        writer=csv.writer(f)
        writer.writerow(['q','m','epsilon^0','epsilon^1','epsilon^2','epsilon^3','epsilon^4'])
        writer.writerows(sample)
    report={
        'status':'PASS','exact_assertions':CHECKS,'python':platform.python_version(),
        'arithmetic':'fractions.Fraction (no floating point)',
        'koenigs_q':list(range(1,9)),'koenigs_m_max':mmax,'epsilon_coefficients_through':order,
        'schroeder_residual_through_epsilon':order+1,
        'log_derivation_q':list(range(1,7)),'log_derivation_monomials':list(range(7)),
        'log_derivation_through_epsilon':6,
        'warning':'Finite symbolic checks are not machine-checked proofs of the infinite theorems.'}
    (data/'verification.json').write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8')
    print(json.dumps(report,indent=2))

if __name__=='__main__':
    main()
