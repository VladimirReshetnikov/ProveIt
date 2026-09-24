#!/usr/bin/env python3
"""Finite exact algebra checks used in the proof; requires SymPy.

These are certificates for explicit algebraic reductions, not a replacement
for the all-index proof in article.tex. Run from any working directory.
"""
from __future__ import annotations
import argparse
import json
from pathlib import Path
import sympy as sp


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path,
                        default=Path(__file__).resolve().parents[1]/'data')
    args = parser.parse_args()
    results = []

    def certify(name: str, expression: sp.Expr) -> None:
        reduced = sp.factor(expression)
        if reduced != 0:
            raise AssertionError((name, reduced))
        results.append({'name': name, 'residual': '0'})

    X,x = sp.symbols('X x')
    u,R,B,t,r,s = sp.symbols('u R B t r s')
    S = X**3-2*u*X**2+(u*u-R)*X-B+t
    A = S-2*t
    certify('Square completion', S**2-4*t*X*(X-u)**2-A**2+4*t*(R*X+B))
    certify('Initial norm factorization', t*(A+t)+t*(R*X+B)-t*X*(X-u)**2)
    gamma = t**3*(B*(B+u*R)**2+t*R**3)
    certify('Curve coefficient equals compact gamma',
            gamma+(t*R)**3*A.subs(X,-B/R))
    original = t**3*(r**3*t+r**2*(s+7*t)
        +2*r*(s*s+2*(t+1)*s+t*(t+8))+s**3+s*s*(3*t+4)
        +s*(t+2)*(3*t+2)+t*(t*t+4*t+12))
    certify('Barry expanded gamma equals compact gamma',
            original-gamma.subs({u:1,R:r+2,B:s+t}))

    a,b,c,p,k,lam,mu = sp.symbols('a b c p k lambda mu')
    cub = X**3+a*X**2+b*X+c
    P = p*X+k
    Q = X**2+lam*X+mu
    ell1 = a*p+k-lam*p
    ell0 = a*k-a*lam*p+b*p-k*lam+lam*lam*p-mu*p+p*p
    L = p*X**2+ell1*X+ell0
    v = ell1*mu+ell0*lam-c*p-b*k-2*p*k
    m = ell0*mu-c*k-k*k
    certify('Universal monic polynomial division', P*(cub+P)+v*X+m-Q*L)
    Gamma = m**3-a*v*m*m+b*v*v*m-c*v**3
    certify('Universal invariant clears its denominator', Gamma+v**3*cub.subs(X,-m/v))
    spec = {a:-2*u,b:u*u-R,c:-B-t,p:0,k:t,lam:-u,mu:0}
    certify('Specialization v=tR', v.subs(spec)-t*R)
    certify('Specialization m=tB', m.subs(spec)-t*B)
    certify('Specialization L=t(X-u)', L.subs(spec)-t*(X-u))
    certify('Universal invariant specializes to main coefficient',Gamma.subs(spec)-gamma)

    # A coefficient comparison in the local continued-fraction proof.
    lp,ln,mup,mun,dm,d = sp.symbols('lambda_prev lambda_n mu_prev mu_n d_prev d_n')
    e = lp+ln-a
    mu_prev_expr = dm+d-a*lp+lp**2+b
    mu_n_expr = b+a*e+d-lp*ln-mu_prev_expr
    certify('q_n(-e_n)=-d_(n-1)', e**2-ln*e+mu_n_expr+dm)

    # Telescoping exponent identities in algebraically independent Hankel terms.
    H = {j:sp.Symbol(f'H{j+3}') for j in range(-3,4)}
    dH = {j:H[j-1]*H[j+1]/H[j]**2 for j in range(-2,3)}
    certify('Five d-factors telescope to width six',
        dH[-2]*dH[-1]**2*dH[0]**3*dH[1]**2*dH[2]-H[-3]*H[3]/H[0]**2)
    certify('Three d-factors telescope to width four',
        dH[-1]*dH[0]**2*dH[1]-H[-2]*H[2]/H[0]**2)

    # Initial determinants, expanded independently from the functional equation.
    g = []
    for n in range(7):
        val = int(n==0)-u*int(n==1)
        if n>=1: val += 2*u*g[n-1]
        if n>=2: val += (R-u*u)*g[n-2]
        if n>=3: val += (B-t)*g[n-3]+t*sum(g[j]*g[n-3-j] for j in range(n-2))
        if n>=4: val -= u*t*sum(g[j]*g[n-4-j] for j in range(n-3))
        g.append(sp.expand(val))
    initial = {2:R,3:-B*(B+u*R),4:-t*(B*(B+u*R)**2+t*R**3)}
    for n,target in initial.items():
        Hn = sp.det(sp.Matrix(n,n,lambda i,j:g[i+j]))
        certify(f'Symbolic initial determinant H_{n}',Hn-target)

    args.output.mkdir(parents=True,exist_ok=True)
    report={'status':'PASS','sympy':sp.__version__,'certificate_count':len(results),
            'certificates':results,'scope':'Finite algebra certificates; see article for all-index proof'}
    (args.output/'symbolic_certificates.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report,indent=2))

if __name__=='__main__':
    main()
