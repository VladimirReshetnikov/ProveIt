#!/usr/bin/env python3
"""Exact finite checks for the logarithmic-degree manuscript.

This is a regression suite, not a proof of the infinite-support theorems.
All mathematical comparisons use exact SymPy integers/rationals.
Run: python verification/verify.py
"""
from __future__ import annotations
import json
import platform
import random
from collections import Counter
from pathlib import Path
import sympy as sp
from sympy.matrices.normalforms import smith_normal_form

SEED = 20260929
rng = random.Random(SEED)
COUNTS: Counter[str] = Counter()
t, z, L, T, a = sp.symbols('t z L T a')


def check(condition: bool, category: str, message: str = '') -> None:
    if not condition:
        raise AssertionError(f'{category}: {message}')
    COUNTS[category] += 1


def zero(M: sp.MatrixBase) -> bool:
    return all(sp.expand(x) == 0 for x in M)


def toeplitz(coeff: list[sp.Matrix], degree: int) -> sp.Matrix:
    """Matrix of M(d/dT) on divided-power polynomials of degree <= degree."""
    r = coeff[0].rows
    Z = sp.zeros(r)
    return sp.BlockMatrix([
        [coeff[j-i] if 0 <= j-i < len(coeff) else Z
         for j in range(degree+1)] for i in range(degree+1)
    ]).as_explicit()


def in_image(A: sp.Matrix, b: sp.Matrix) -> bool:
    return A.rank() == A.row_join(b).rank()


def polynomial_coefficients(M: sp.Matrix, degree: int) -> list[sp.Matrix]:
    return [M.applyfunc(lambda q: sp.expand(q).coeff(z, k))
            for k in range(degree+1)]


def valuation(poly: sp.Expr) -> int:
    p = sp.Poly(poly, z)
    if p.is_zero:
        raise ValueError('The zero polynomial has no finite valuation.')
    return min(mon[0] for mon, c in p.terms() if c != 0)


def scalar_realization(B: sp.Matrix) -> tuple[sp.Expr, sp.Matrix, dict[int, sp.Expr]]:
    """Return the exact scalar Euler operator's indicial data and q_eta."""
    r = B.rows
    if B.cols != r or any(B[i,j] != 0 for i in range(r) for j in range(i+1)):
        raise ValueError('B must be square and strictly upper triangular.')
    P = sp.prod(t-j for j in range(r))
    dp = [sp.diff(P,t).subs(t,j) for j in range(r)]
    lag = [sp.prod(t-k for k in range(r) if k != j)/dp[j]
           for j in range(r)]
    q = {eta: sp.expand(sum(dp[j-eta]*B[j-eta,j]*lag[j]
                            for j in range(eta,r)))
         for eta in range(1,r)}
    return sp.expand(P), sp.diag(*dp), q


def reconstruct_B(r: int, D: sp.Matrix, q: dict[int, sp.Expr]) -> sp.Matrix:
    return sp.Matrix(r,r,lambda i,j:
        sp.cancel(q[j-i].subs(t,j)/D[i,i]) if i < j and j-i in q else 0)


def moment_checks() -> None:
    # At n=1, sigma=L^-1. Higher-depth identities are proved, not sampled.
    for m in range(1,9):
        C = sp.zeros(m)
        for j in range(m):
            for k in range(m):
                H = sum(sp.diff(L**-1 * sp.diff(L**k,L,m-1-h),L,h)
                        for h in range(m))
                got = sp.expand(L**j * H).coeff(L,-1)
                expected = (-1)**j*sp.factorial(j)*sp.factorial(k) if j+k==m-1 else 0
                check(got == expected, 'residue_moment_entries', f'm={m},j={j},k={k}')
                C[j,k] = got
        check(C.det() == sp.prod(sp.factorial(k)**2 for k in range(m)),
              'residue_determinants', str(m))
        # An independently formed nonconstant Q(delta) on polynomials.
        q0 = sp.Rational(m+1, m+2)
        Qop = sp.zeros(m)
        for k in range(m):
            expr = q0*L**k + 2*sp.diff(L**k,L) - sp.diff(L**k,L,2)
            for j in range(m):
                Qop[j,k] = sp.expand(expr).coeff(L,j)
        check((C*Qop).det() == q0**m*sp.prod(sp.factorial(k)**2 for k in range(m)),
              'multiple_root_crossing_determinants', str(m))


def random_pencil_checks() -> list[dict]:
    records = []
    for case in range(30):
        r = 1 + case % 6
        B = sp.Matrix(r,r,lambda i,j: sp.Rational(rng.randint(-3,3),rng.randint(1,3)) if i<j else 0)
        P,D,q = scalar_realization(B)
        check(zero(reconstruct_B(r,D,q)-B), 'scalar_realizations', str(case))
        for eta,poly in q.items():
            check(poly==0 or sp.degree(poly,t) <= r-1, 'interpolation_degree_bounds')
            for j in range(r):
                expected = D[j-eta,j-eta]*B[j-eta,j] if j>=eta else 0
                check(sp.expand(poly.subs(t,j)-expected)==0, 'interpolation_values')
        d = sp.Matrix([rng.randint(-2,2) for _ in range(r)])
        Mcoeff = [D*B,D]
        b = D*d
        min_toeplitz = None
        min_image = None
        profile = []
        for p in range(r+1):
            A = toeplitz(Mcoeff,p)
            rhs = sp.Matrix.vstack(b,sp.zeros(r*p,1))
            h = r*(p+1)-A.rank()
            expected_h = r-(B**(p+1)).rank()
            check(h == expected_h, 'pencil_homogeneous_filtrations', f'{case}/{p}')
            profile.append(h)
            solved = in_image(A,rhs)
            criterion = in_image(B**(p+1),(B**p)*d)
            check(solved == criterion, 'pencil_forcing_degree_tests', f'{case}/{p}')
            if solved and min_toeplitz is None:
                min_toeplitz = p
            if criterion and min_image is None:
                min_image = p
        check(min_toeplitz == min_image, 'pencil_minimum_degrees')
        c = sum(((-1)**j*(B**j)*d*T**(j+1)/sp.factorial(j+1)
                 for j in range(r)),sp.zeros(r,1))
        check(zero(c.diff(T)+B*c-d), 'pencil_particular_residuals')
        records.append({'case':case,'size':r,'h':profile,'minimum_degree':min_toeplitz})
    return records


def general_series_checks() -> list[dict]:
    records=[]
    # Polynomial representatives of more general formal upper triangular series.
    # The diagonal is z times a unit, so det has valuation r and inverse pole <= r.
    for case in range(12):
        r=2+case%4
        M=sp.zeros(r)
        for i in range(r):
            M[i,i]=z*(1+rng.randint(-2,2)*z+rng.randint(0,2)*z**2)
            for j in range(i+1,r):
                M[i,j]=sum(rng.randint(-2,2)*z**k for k in range(3))
        S=smith_normal_form(M,domain=sp.QQ.poly_ring(z))
        nu=sorted(valuation(S[i,i]) for i in range(r))
        check(sum(nu)==r and max(nu)<=r,'general_smith_bounds',str(case))
        coeff=polynomial_coefficients(M,r)
        h=[]
        for p in range(r):
            H=r*(p+1)-toeplitz(coeff,p).rank()
            check(H==sum(min(p+1,n) for n in nu),'general_smith_toeplitz_filtrations',f'{case}/{p}')
            h.append(H)
        increments=[h[0]]+[h[i]-h[i-1] for i in range(1,r)]
        recovered=[0]*(r-h[0])
        for k in range(1,r+1):
            recovered += [k]*(increments[k-1]-(increments[k] if k<r else 0))
        check(recovered==nu,'general_smith_reconstruction',str(case))
        check(valuation(M.det())==r,'general_determinant_valuations')
        records.append({'case':case,'size':r,'smith_valuations':nu,'h':h})
    return records


def diamond_checks() -> dict:
    B=sp.Matrix([[0,1,1,0],[0,0,0,1],[0,0,0,a],[0,0,0,0]])
    P,D,q=scalar_realization(B)
    q1=-t*(t-2)*((a+9)*t-a-27)/3
    q2=t*(t-1)*(10*t-29)/3
    check(sp.expand(q[1]-q1)==0,'diamond_symbolic')
    check(sp.expand(q[2]-q2)==0 and q[3]==0,'diamond_symbolic')
    e=sp.zeros(4); e[0,3]=1
    check(zero(B**2-(a+1)*e),'diamond_symbolic')
    check(zero((D*B)**2-12*(a-1)*e),'diamond_symbolic')
    check(zero(B**3),'diamond_symbolic')
    d=sp.Matrix([0,0,0,1])
    c=sp.Matrix([(1+a)*T**3/6,-T**2/2,-a*T**2/2,T])
    check(zero(c.diff(T)+B*c-d),'diamond_symbolic')
    rows=[]
    certificates=[]
    for av in [-2,-1,0,1,2]:
        Bv=B.subs(a,av); b=D*d
        profile=[]; minimum=None
        for p in range(5):
            A=toeplitz([D*Bv,D],p)
            rhs=sp.Matrix.vstack(b,sp.zeros(4*p,1))
            profile.append(4*(p+1)-A.rank())
            if in_image(A,rhs) and minimum is None:
                minimum=p
        expect_min=2 if av==-1 else 3
        expected_h=[2,4,4,4,4] if av==-1 else [2,3,4,4,4]
        check(minimum==expect_min and profile==expected_h,'diamond_degrees',str(av))
        # Export a exact finite left-nullspace obstruction at degree minimum-1.
        p=minimum-1
        A=toeplitz([D*Bv,D],p)
        rhs=sp.Matrix.vstack(b,sp.zeros(4*p,1))
        w=next(w for w in A.T.nullspace() if (w.T*rhs)[0]!=0)
        check(zero(w.T*A) and (w.T*rhs)[0]!=0,'diamond_obstruction_certificates')
        certificates.append({'a':av,'ruled_out_degree':p,
            'left_nullvector':[str(v) for v in w],
            'pairing':str((w.T*rhs)[0])})
        rows.append({'a':av,'h':profile,'minimum_degree':minimum})
    return {'P':str(P),'D':[str(D[i,i]) for i in range(4)],
            'q1':str(sp.factor(q1)),'q2':str(sp.factor(q2)),
            'specializations':rows,'certificates':certificates}


def partitions(n: int, maxpart: int | None = None):
    if n==0:
        yield []
        return
    m=min(n,maxpart or n)
    for p in range(m,0,-1):
        for rest in partitions(n-p,p):
            yield [p]+rest


def partition_checks() -> int:
    count=0
    for r in range(1,8):
        for parts in partitions(r):
            blocks=[sp.Matrix(q,q,lambda i,j: int(j==i+1)) for q in parts]
            B=sp.diag(*blocks)
            P,D,q=scalar_realization(B)
            check(zero(reconstruct_B(r,D,q)-B),'all_partition_realizations')
            for p in range(r):
                h=r-(B**(p+1)).rank()
                check(h==sum(min(p+1,j) for j in parts),'all_partition_filtrations')
            count+=1
    return count


def main() -> None:
    moment_checks()
    pencil=random_pencil_checks()
    general=general_series_checks()
    diamond=diamond_checks()
    partition_count=partition_checks()
    result={
        'status':'PASS','seed':SEED,'arithmetic':'exact integers and rationals; no floating-point tests',
        'python_version':platform.python_version(),'sympy_version':sp.__version__,
        'assertions':sum(COUNTS.values()),'counts':dict(sorted(COUNTS.items())),
        'random_pencil_cases':pencil,'general_polynomial_matrix_cases':general,
        'partition_cases':partition_count,'diamond':diamond,
        'scope':'Finite symbolic checks only. Not a Lean formalization or verification of arbitrary Hahn supports.'}
    out=Path(__file__).resolve().parent/'results.json'
    out.write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
    print(json.dumps({'status':result['status'],'assertions':result['assertions'],
                      'counts':result['counts'],'results_file':str(out)},indent=2))

if __name__=='__main__':
    main()
