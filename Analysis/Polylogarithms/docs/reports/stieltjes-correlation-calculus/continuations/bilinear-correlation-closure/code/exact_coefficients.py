#!/usr/bin/env python3
"""Exact coefficient engine for the Stieltjes correlation closure theorem.

This program verifies finite algebra, not the analytic theorem. Zeta values
are kept as formal symbols z2,z3,...; no independence is asserted.
"""
from __future__ import annotations
import argparse, json, math
from pathlib import Path
import sympy as sp

u,v,L = sp.symbols('u v L')

def homogeneous_A(max_degree: int) -> list[sp.Expr]:
    if max_degree < 0:
        raise ValueError('max_degree must be nonnegative')
    logs = [sp.S.Zero]*(max_degree+1)
    for k in range(2,max_degree+1):
        logs[k] = sp.expand(sp.Symbol(f'z{k}')/k*((-1)**k*((u+v)**k-u**k)+v**k))
    out = [sp.S.One]+[sp.S.Zero]*max_degree
    for d in range(1,max_degree+1):
        out[d] = sp.expand(sum(k*logs[k]*out[d-k] for k in range(2,d+1))/d)
    return out

def swap(expr: sp.Expr) -> sp.Expr:
    return expr.xreplace({u:v,v:u})

def coeff(expr: sp.Expr, i: int, j: int) -> sp.Expr:
    return sp.expand(expr).coeff(u,i).coeff(v,j)

def row(m: int,n: int,A: list[sp.Expr]) -> dict:
    if m<0 or n<0 or len(A)<=m+n+2:
        raise ValueError('nonnegative indices and sufficient A degrees are required')
    D=m+n+2; N=D-1
    B=[swap(x) for x in A]
    Q,rem=sp.div(u*A[D]+v*B[D],u+v,u)
    if sp.expand(rem)!=0:
        raise AssertionError('Q numerator is not divisible by u+v')
    factor=(-1)**(m+n)*sp.factorial(m)*sp.factorial(n)
    c=sp.expand(-factor*coeff(Q,m+1,n+1))
    ca=[]; cb=[]
    for j in range(N+1):
        common=-factor*(-1)**j/sp.factorial(j)*(u+v)**j
        ca.append(sp.expand(coeff(common*v*B[N-j],m+1,n+1)))
        cb.append(sp.expand(coeff(common*u*A[N-j],m+1,n+1)))
    P=0
    for d in range(N+1):
        P += coeff(B[d]*(-(u+v)*L)**(N-d)/sp.factorial(N-d),m+1,n)
    P=sp.expand(-factor*P)
    return {'m':m,'n':n,'constant':c,'a':ca,'b':cb,'collision':P}

def formula(r:dict) -> sp.Expr:
    return sp.expand(r['constant']+sum(c*sp.Symbol(f'a{j}') for j,c in enumerate(r['a']))+sum(c*sp.Symbol(f'b{j}') for j,c in enumerate(r['b'])))

def verify(rows:list[dict]) -> int:
    checks=0; by={(r['m'],r['n']):r for r in rows}
    for r in rows:
        m,n=r['m'],r['n']; N=m+n+1; s=by[n,m]
        assert sp.expand(r['constant']-s['constant'])==0; checks+=1
        assert all(sp.expand(x-y)==0 for x,y in zip(r['a'],s['b'])); checks+=1
        assert r['a'][N]==sp.Rational(1,m+1); checks+=1
        assert r['b'][N]==sp.Rational(1,n+1); checks+=1
        assert r['a'][N-1]==r['b'][N-1]==0; checks+=1
        assert sp.expand(r['collision']).coeff(L,N)==sp.Rational(1,m+1); checks+=1
    assert sp.expand(formula(by[0,0])-(sp.Symbol('a1')+sp.Symbol('b1')-2*sp.Symbol('z2')))==0; checks+=1
    target=sp.Symbol('a2')/2+sp.Symbol('b2')+sp.Symbol('z2')*(sp.Symbol('a0')+sp.Symbol('b0'))-sp.Symbol('z3')
    assert sp.expand(formula(by[1,0])-target)==0; checks+=1
    return checks

def serializable(r:dict) -> dict:
    return {k:([str(t) for t in x] if isinstance(x,list) else str(x) if isinstance(x,sp.Expr) else x) for k,x in r.items()}

def main() -> None:
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--max-total',type=int,default=8)
    parser.add_argument('--output',type=Path,default=Path(__file__).resolve().parents[1]/'results')
    args=parser.parse_args()
    if not 1<=args.max_total<=12:
        parser.error('--max-total must lie between 1 and 12')
    A=homogeneous_A(args.max_total+2)
    rows=[row(m,N-m,A) for N in range(args.max_total+1) for m in range(N+1)]
    checks=verify(rows)
    args.output.mkdir(parents=True,exist_ok=True)
    data={'schema':'stieltjes-correlation-closure-v1','conventions':{'a_j':'gamma_j(a)','b_j':'gamma_j(1-a)','z_k':'Riemann zeta(k)','L':'log(a), in collision polynomials only'},'max_total':args.max_total,'exact_checks':checks,'rows':[serializable(r) for r in rows]}
    (args.output/'coefficients.json').write_text(json.dumps(data,indent=2)+'\n')
    text=['# Exact correlation identities','', 'a_j = gamma_j(a); b_j = gamma_j(1-a); z_k = zeta(k).','']
    for r in rows:
        text += [f"I_{r['m']},{r['n']}(a) = {formula(r)}",f"Collision polynomial = {r['collision']}",'']
    (args.output/'identities.txt').write_text('\n'.join(text))
    summary={'status':'PASS','rows':len(rows),'exact_checks':checks,'max_total':args.max_total,'sympy_version':sp.__version__,'scope':'Finite symbolic algebra only; the analytic proof is in article.tex.'}
    (args.output/'exact_verification.json').write_text(json.dumps(summary,indent=2)+'\n')
    print(json.dumps(summary,indent=2))
    for r in rows:
        if r['m']+r['n']<=3 and r['m']>=r['n']:
            print(f"I{r['m']}{r['n']} =",formula(r))

if __name__=='__main__':
    main()
