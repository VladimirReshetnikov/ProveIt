#!/usr/bin/env python3
"""Exact finite certificates for Nested Harmonic Jets (Python 3, SymPy).
These check algebraic instances. Analytic convergence is proved in article.tex.
"""
from __future__ import annotations
import json, math, time
from pathlib import Path
import sympy as S

ROOT=Path(__file__).resolve().parents[1]
OUT=ROOT/'results'; OUT.mkdir(exist_ok=True)
checks=[]
def check(name: str, value) -> None:
    residual=S.expand(value)
    if residual != 0:
        residual=S.simplify(residual)
    if residual != 0:
        raise AssertionError(f'{name}: {residual}')
    checks.append(name)

def multiply(A: dict, B: dict, lo: int, hi: int) -> dict:
    C={}
    for i,a in A.items():
        for j,b in B.items():
            if lo<=i+j<=hi:
                C[i+j]=C.get(i+j,0)+a*b
    return {i:S.expand(c) for i,c in C.items() if c!=0}

def add(A:dict,B:dict,scale=1) -> dict:
    C=A.copy()
    for i,b in B.items(): C[i]=C.get(i,0)+scale*b
    return {i:S.expand(c) for i,c in C.items() if c!=0}

def depth_coeffs(D:int,K:int,regular:bool) -> list[dict]:
    p={1:{r:(-1)**r*S.Symbol(f'g{r}')/S.factorial(r) for r in range(K+1)}}
    if not regular: p[1][-1]=S.Integer(1)
    for k in range(2,D+1):
        p[k]={r:k**r*S.Symbol(f'Z{k}_{r}')/S.factorial(r) for r in range(K+1)}
    E=[{0:S.Integer(1)}]
    for d in range(1,D+1):
        row={}
        for k in range(1,d+1):
            row=add(row,multiply(p[k],E[d-k],-D,K),S.Rational((-1)**(k-1),d))
        E.append(row)
    return E

def main() -> None:
    start=time.time()
    # Elementary symmetric functions: direct product versus Newton sums.
    z=S.Symbol('z')
    for N in range(1,11):
        xs=[S.Rational(1,n+1) for n in range(N)]
        poly=S.Poly(S.prod(1+z*x for x in xs),z)
        E=[S.Integer(1)]
        for d in range(1,N+1):
            E.append(S.expand(sum((-1)**(k-1)*sum(x**k for x in xs)*E[d-k] for k in range(1,d+1))/d))
        for d in range(N+1): check(f'Newton_N{N}_d{d}',E[d]-poly.nth(d))
    print('Newton checks complete',flush=True)
    # Laurent finite part versus pole-subtracted depth coefficient.
    D,R=4,2;K=D+R
    raw=depth_coeffs(D,K,False); reg=depth_coeffs(D,K,True)
    print('Symbolic Laurent arrays constructed',flush=True)
    for d in range(D+1):
        for r in range(-d,R+1):
            rhs=sum(reg[d-j].get(r+j,0)/S.factorial(j) for j in range(d+1))
            check(f'regulator_d{d}_r{r}',raw[d].get(r,0)-rhs)
    table={str(d):{'harmonic_regularized':str(reg[d].get(0,0)),
                   'diagonal_finite_part':str(raw[d].get(0,0)),
                   'anomaly':str(S.expand(raw[d].get(0,0)-reg[d].get(0,0)))}
           for d in range(1,D+1)}
    (OUT/'finite_parts.json').write_text(json.dumps({'notation':'g_r=gamma_r(a); Zk_r=zeta^(r)(k,a), spectral derivative','rows':table},indent=2)+'\n')
    # Finite first-order resonance polynomials, independently checked by ODE.
    w=S.Symbol('w'); resonance={}
    for m in range(1,13):
        # Keep logarithms as independent exact symbols; log(1)=0.
        logs={k:(S.Integer(0) if k==1 else S.Symbol(f'ell{k}')) for k in range(1,m+1)}
        lm=logs[m]; Q=S.Integer(0)
        for n in range(1,m+1):
            I=S.Integer(0)
            for j in range(n):
                if j==m-1: continue # logarithmic contribution separated below
                I+=(-1)**j*S.binomial(n-1,j)*((1-w)**m-(1-w)**(j+1))/S.Rational(j-m+1)
            Q+=(-1)**n*S.binomial(m,n)*n*logs[n]*I
        P=S.expand(-Q)
        assert S.denom(P)==1
        P=S.Poly(S.expand(P),w).as_expr()
        T=P-m*lm*(1-w)**m*S.log(1-w)
        forcing=sum((-1)**n*S.binomial(m,n)*n*logs[n]*w**(n-1) for n in range(1,m+1))
        check(f'resonance_ODE_m{m}',(1-w)*S.diff(P,w)+m*P+m*lm*(1-w)**m+(1-w)*forcing)
        check(f'resonance_origin_m{m}',T.subs(w,0))
        # Taylor coefficients of the explicit log formula, against the product derivative.
        for n in range(1,49):
            logcoeff=-sum((-1)**j*S.binomial(m,j)/S.Rational(n-j) for j in range(min(m,n-1)+1))
            lhs=S.expand(P).coeff(w,n)-m*lm*logcoeff
            if n<=m:
                rhs=(-1)**n*S.binomial(m,n)*(-logs[n]+m*sum(logs[k]/S.Rational(k-m) for k in range(1,n)))
            else:
                rhs=S.Rational((-1)**m*m,(n-m)*S.binomial(n,m))*lm
            check(f'resonance_coefficient_m{m}_n{n}',lhs-rhs)
        print('Resonance',m,flush=True)
        if m<=6: resonance[str(m)]={'polynomial':str(P),'log_coefficient':str(-m*lm*(1-w)**m)}
    (OUT/'resonance_polynomials.json').write_text(json.dumps(resonance,indent=2)+'\n')
    # Negative-integer polylog recurrence, rational functions, to order 8.
    t=S.Symbol('t'); rat=-t/(1+t)
    for r in range(1,9):
        if r>1: rat=S.cancel(t*S.diff(rat,t))
        direct=sum(S.Integer(-1)**k*S.Integer(k)**(r-1)*t**k for k in range(1,18))
        coeffs=S.series(rat,t,0,18).removeO()
        for k in range(1,18): check(f'negative_polylog_r{r}_k{k}',coeffs.coeff(t,k)-direct.coeff(t,k))
    report={'status':'PASS','assertions':len(checks),'seconds':time.time()-start,
            'sympy_version':S.__version__,'checks':checks,
            'scope':'Finite exact algebra checks. Not a proof-assistant formalization.'}
    (OUT/'exact_verification.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps({k:v for k,v in report.items() if k!='checks'},indent=2))

if __name__=='__main__':main()
