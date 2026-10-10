#!/usr/bin/env python3
"""Finite exact checks of the polynomial identities and sample tables.

These are regression tests for formulas with analytic proofs in article.pdf;
they are neither a proof assistant nor finite evidence substituted for proof.
"""
from __future__ import annotations
import json, platform, time
from pathlib import Path
import sympy as s
from gauss_hurwitz import coefficient_jets, path_coefficient_jets, residue

ROOT=Path(__file__).resolve().parents[1]
checks=[]

def zero(name, expr):
    result=s.expand(expr)
    if result != 0:
        result=s.simplify(result)
    if result != 0:
        raise AssertionError(f'{name}: {result}')
    checks.append(name)


def main():
    start=time.time()
    a,b,c,u,d=s.symbols('a b c u d')
    A=[row[0] for row in coefficient_jets(a,b,c,u,5,0)]
    zero('printed A1',A[1]-(c-a*b+(c-a-b+s.Rational(1,2))*u-u*u/2))
    for j in range(1,5):
        zero(f'shift differential j={j}',s.diff(A[j],c)-(u+j)*A[j-1])
        z=sum(-s.bernoulli(k,c)/k*A[j-k] for k in range(1,j+1))
        zero(f'parameter differential j={j}',s.diff(A[j],a)+s.diff(A[j],b)-s.diff(A[j],u)
             +(u+j)*A[j-1]-z)
        shift=sum(A[l].subs(c,d)*s.rf(1+u+l,j-l)*(c-d)**(j-l)/s.factorial(j-l)
                  for l in range(j+1))
        zero(f'finite reference change j={j}',A[j]-shift)
    for N in range(5):
        rho=residue(a,b,N)
        zero(f'generic residue N={N}',A[N].subs(u,-N)-rho)
        low=sum(A[j].subs(u,-N)*(-s.bernoulli(N-j,c)/(N-j)) for j in range(N))
        zero(f'generic resonant coefficient N={N}',s.diff(A[N],u).subs(u,-N)+low
             -s.diff(rho,a)-s.diff(rho,b))
    pairs=[('1/2','1/2'),('1/3','2/3'),('2/3','5/4'),(1,'1/2'),(2,3)]
    for av,bv in pairs:
        for cv in ['1/3',1,'7/4']:
            for N in range(9):
                aa=coefficient_jets(av,bv,cv,-N,N+1,1)
                rho=residue(av,bv,N)
                zero(f'rational residue {av},{bv},{cv},N={N}',aa[N][0]-rho)
                generic=residue(a,b,N)
                deriv=(s.diff(generic,a)+s.diff(generic,b)).subs({a:s.sympify(av),b:s.sympify(bv)})
                low=sum(aa[j][0]*(-s.bernoulli(N-j,s.sympify(cv))/(N-j)) for j in range(N))
                zero(f'rational resonant coefficient {av},{bv},{cv},N={N}',aa[N][1]+low-deriv)
    for N in range(4):
        x=coefficient_jets('1/3','2/3','7/4',-N,10,4)
        y=path_coefficient_jets('1/3','2/3','7/4',-N,0,0,1,10,4)
        for j in range(10):
            for q in range(5):
                zero(f'independent path jet N={N},j={j},q={q}',x[j][q]-y[j][q])
    # Polynomial factor in the entire reciprocal-Gamma expansion.
    t=s.symbols('t')
    for k in range(9):
        prod=s.sympify(s.prod(t-r for r in range(1,k+1)))
        zero(f'reciprocal Gamma polynomial k={k}',prod-(-1)**k*s.factorial(k)*s.prod(1-t/r for r in range(1,k+1)))
        zero(f'revival leading coefficient k={k}',prod.subs(t,0)-(-1)**k*s.factorial(k))
    table=[]
    for N in range(11):
        aa=coefficient_jets('1/2','1/2',1,-N,N+1,0)
        rho=residue('1/2','1/2',N)
        table.append({'N':N,'rho':str(rho),'rational_part':str(rho*s.harmonic(N)),
                      'log2_coefficient':str(4*rho),'subtraction_coefficients':[str(row[0]) for row in aa]})
    # Deliberate canary: the wrong sign in A1 must be rejected.
    bad=A[1]+s.Rational(1,2)
    try:
        zero('deliberately mutated A1',bad-A[1])
    except AssertionError:
        checks.append('wrong A1 canary rejected')
    else:
        raise AssertionError('mutation canary was not rejected')
    result={'status':'PASS','exact_check_count':len(checks),'checks':checks,
            'python':platform.python_version(),'sympy':s.__version__,
            'elapsed_seconds':round(time.time()-start,3),
            'scope':'Finite exact regression checks; general results are proved analytically in article.pdf.'}
    (ROOT/'results').mkdir(exist_ok=True)
    (ROOT/'results'/'exact_checks.json').write_text(json.dumps(result,indent=2)+'\n')
    (ROOT/'results'/'central_binomial_table.json').write_text(json.dumps(table,indent=2)+'\n')
    print(f'PASS: {len(checks)} exact checks; table N=0,...,10; {result["elapsed_seconds"]} s')

if __name__=='__main__':
    main()
