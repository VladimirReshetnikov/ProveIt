#!/usr/bin/env python3
"""Exact finite checks for the accompanying Hahn--Fredholm research article.

These checks do not prove infinite-dimensional or arbitrary-support assertions.
Run: python code/verify.py --output data/verification.json
Requires Python >= 3.10 and SymPy (tested with 1.14.0).
"""
from __future__ import annotations
import argparse
from collections import Counter
from datetime import datetime, timezone
import json
from pathlib import Path
import platform
import random
import time
import sympy as s

SEED = 20260922
COUNTS: Counter[str] = Counter()

def check(category: str, condition: bool) -> None:
    if not condition:
        raise AssertionError(f"Check failed in {category}, after {dict(COUNTS)}")
    COUNTS[category] += 1

def zero(n: int) -> s.Matrix:
    return s.zeros(n)

def mul(a: list[s.Matrix], b: list[s.Matrix], q: int) -> list[s.Matrix]:
    n = a[0].rows
    return [sum((a[j] * b[k-j] for j in range(k+1)), zero(n))
            for k in range(q+1)]

def randmat(rng: random.Random, n: int, symmetric: bool = False) -> s.Matrix:
    m = s.Matrix(n, n, lambda i,j: s.Rational(rng.randint(-3,3),rng.randint(1,4)))
    return m + m.T if symmetric else m

def eigen_coeffs(d: list[s.Rational], a: list[s.Matrix], index: int,
                 q: int) -> tuple[list[s.Expr], list[s.Matrix]]:
    n = len(d)
    e = s.eye(n)[:, index]
    u = [e]
    ell: list[s.Expr] = [d[index]]
    for k in range(1,q+1):
        w = sum((a[j]*u[k-j] for j in range(1,k+1)),s.zeros(n,1))
        w -= sum((ell[j]*u[k-j] for j in range(1,k)),s.zeros(n,1))
        ell.append(w[index])
        u.append(s.Matrix([0 if j==index else -w[j]/(d[j]-d[index])
                           for j in range(n)]))
    return ell,u

def run() -> dict:
    COUNTS.clear()
    start=time.monotonic()
    rng=random.Random(SEED)
    q=6
    systems=0
    for trial in range(24):
        n=2+trial%4
        d=[s.Rational(1,2**(j+1)) for j in range(n)]
        a=[s.diag(*d),randmat(rng,n,True),randmat(rng,n,True)]
        a += [zero(n) for _ in range(q-2)]
        for index in range(n):
            ell,u=eigen_coeffs(d,a,index,q)
            for k in range(q+1):
                residual=sum((a[j]*u[k-j]-ell[j]*u[k-j]
                              for j in range(k+1)),s.zeros(n,1))
                check('eigen_equation_coefficient', residual==s.zeros(n,1))
            check('eigenvector_gauge', all(v[index]==0 for v in u[1:]))
            expected=a[2][index,index]+sum(
                a[1][index,j]*a[1][j,index]/(d[index]-d[j])
                for j in range(n) if j!=index)
            check('second_order_rayleigh_formula', s.simplify(ell[2]-expected)==0)
        systems+=1

    t=s.Symbol('t')
    for trial in range(12):
        n=2+trial%2
        b=randmat(rng,n)
        c=randmat(rng,n)
        e=[zero(n),b,c]+[zero(n) for _ in range(q-2)]
        power=[s.eye(n)]+[zero(n) for _ in range(q)]
        log=[zero(n) for _ in range(q+1)]
        for k in range(1,q+1):
            power=mul(power,e,q)
            for j in range(q+1):
                log[j]+=s.Rational((-1)**(k+1),k)*power[j]
        logs=[x.trace() for x in log]
        det=[s.Integer(1)]
        for k in range(1,q+1):
            det.append(s.expand(sum(j*logs[j]*det[k-j] for j in range(1,k+1))/k))
        direct=s.Poly((s.eye(n)+t*b+t*t*c).det(),t)
        for k in range(q+1):
            check('trace_log_determinant',s.simplify(det[k]-direct.nth(k))==0)
        # Multivariate Taylor / Sylvester identity (ordinary finite surrogate).
        u=randmat(rng,n)[:,:1]
        v=randmat(rng,n)[:1,:]
        check('sylvester_rank_one',s.expand((s.eye(n)+t*u*v).det()-(1+t*(v*u)[0]))==0)

    for trial in range(8):
        n=3
        p=s.diag(1,0,0)
        k=randmat(rng,n)
        k=k-k.T
        r=[k**j/s.factorial(j) for j in range(q+1)]
        ri=[(-k)**j/s.factorial(j) for j in range(q+1)]
        pp=mul([rj*p for rj in r],ri,q)
        x=[pp[j]-(p if j==0 else zero(n)) for j in range(q+1)]
        x2=mul(x,x,q)
        # W=P(t)P+(1-P(t))(1-P), M=1-(P(t)-P)^2.
        w=[pp[j]*p-pp[j]*(s.eye(n)-p)
           +(s.eye(n)-p if j==0 else zero(n)) for j in range(q+1)]
        factor=[s.eye(n)]+[zero(n) for _ in range(q)]
        power=[s.eye(n)]+[zero(n) for _ in range(q)]
        for j in range(1,q+1):
            power=mul(power,x2,q)
            coefficient=s.binomial(2*j,j)/4**j
            factor=[factor[k0]+coefficient*power[k0] for k0 in range(q+1)]
        u=mul(w,factor,q)
        utu=mul([uj.T for uj in u],u,q)
        inter=mul(pp,u,q)
        for j in range(q+1):
            check('kato_unitary_coefficient',utu[j]==(s.eye(n) if j==0 else zero(n)))
            check('kato_intertwining_coefficient',inter[j]==u[j]*p)

    # Finite-rank correction of a singular residue: M=F+UV is invertible.
    for trial in range(10):
        n=3
        b=randmat(rng,n)
        f=s.diag(0,2,3)+t*b
        u=s.Matrix([1,0,0]); v=u.T
        m=f+u*v
        # determinant lemma in adjugate form avoids a rational inversion.
        rhs=s.expand(m.det()-(v*m.adjugate()*u)[0])
        check('singular_residue_finite_reduction',s.expand(f.det()-rhs)==0)

    # Explicit obstruction example: test exact low-order coefficients.
    for n in range(1,17):
        size=n+2  # all walks of length two from n stay inside this section.
        d=[s.Rational(1,2**(j+1)) for j in range(size)]
        b=zero(size)
        for j in range(size-1):
            b[j,j+1]=b[j+1,j]=s.Rational(1,(j+1)**2)
        ell,_=eigen_coeffs(d,[s.diag(*d),b,zero(size),zero(size)],n-1,3)
        expected=s.Integer(4) if n==1 else 2**n*(s.Rational(2,n**4)-s.Rational(1,(n-1)**4))
        check('obstruction_second_order',ell[2]==expected)
        check('bipartite_odd_coefficients',ell[1]==0 and ell[3]==0)
        forced=b[n-1,n]/(d[n]-d[n-1])
        check('forced_unbounded_generator',forced==-s.Rational(2**(n+1),n*n))
    for n in range(16,81):
        coefficient=2**n*(s.Rational(2,n**4)-s.Rational(1,(n-1)**4))
        check('second_order_growth_lower_bound',coefficient>=s.Rational(2**(n-1),n**4))

    # Exact boundary identities responsible for trace/product failure.
    sum_a=s.Integer(0)
    weighted=s.Integer(0)
    qsum=s.Integer(0)
    for n in range(1,65):
        dn=s.Rational(1,2**n)
        gn=s.Rational(2**(n+1),n**4)
        an=s.Integer(4) if n==1 else 2**n*(s.Rational(2,n**4)-s.Rational(1,(n-1)**4))
        sum_a+=an
        weighted+=an/(1+dn)
        check('spectral_trace_boundary',sum_a==gn)
        check('spectral_product_boundary',weighted==gn/(1+dn)-qsum)
        qsum+=s.Rational(1,n**4)/((1+dn)*(1+s.Rational(1,2**(n+1))))
    for size in range(2,9):
        d=[s.Rational(1,2**j) for j in range(1,size+1)]
        b=zero(size)
        for j in range(size-1):
            b[j,j+1]=b[j+1,j]=s.Rational(1,(j+1)**2)
        k=s.diag(*[1/(1+dj) for dj in d])*b
        qsum=sum(s.Rational(1,j**4)/((1+d[j-1])*(1+d[j]))
                 for j in range(1,size))
        check('finite_section_trace_log_second',(k*k).trace()/2==qsum)
        exact_coeffs=[]
        for index in range(size):
            ell,_=eigen_coeffs(d,[s.diag(*d),b,zero(size)],index,2)
            exact_coeffs.append(ell[2])
        check('finite_section_trace_boundary_cancel',sum(exact_coeffs)==0)
        check('finite_section_product_boundary_cancel',
              sum(exact_coeffs[j]/(1+d[j]) for j in range(size))==-qsum)

    # Finite diagnostic for a genuinely rank-two exponent order.
    eta=(0,1); beta=(1,0)
    for n in range(1,33):
        check('rank_two_noncofinality', (0,n)<beta)
    diagnostics={
        'first_generator_magnitudes':{str(n):str(s.Rational(2**(n+1),n*n))
                                     for n in (4,8,16,32,64)},
        'second_eigenvalue_coefficients':{
            str(n):str(2**n*(s.Rational(2,n**4)-s.Rational(1,(n-1)**4)))
            for n in (4,8,16,32,64)},
    }
    return {
        'status':'PASS','seed':SEED,'python':platform.python_version(),
        'sympy':s.__version__,'random_perturbation_systems':systems,
        'checks':dict(COUNTS),'total_checks':sum(COUNTS.values()),
        'elapsed_seconds':round(time.monotonic()-start,3),
        'generated_utc':datetime.now(timezone.utc).isoformat(),
        'scope':'Exact finite algebra only; not a proof of infinite-dimensional results.',
        'diagnostics':diagnostics,
    }

def main() -> None:
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path,default=Path('data/verification.json'))
    args=parser.parse_args()
    report=run()
    args.output.parent.mkdir(parents=True,exist_ok=True)
    args.output.write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8')
    print(json.dumps(report,indent=2))

if __name__=='__main__':
    main()
