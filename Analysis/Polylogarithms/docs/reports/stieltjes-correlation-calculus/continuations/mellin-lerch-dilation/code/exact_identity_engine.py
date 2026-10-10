#!/usr/bin/env python3
"""Exact finite algebra accompanying the analytic proofs.

All comparisons use rational symbolic arithmetic, not fitted constants.
The negative-order moment audit compares the zeta-side formula with
derivatives of an independently integrated rational polylogarithm.
Run from any working directory; output is written to ../results.
"""
from functools import lru_cache
from pathlib import Path
import json
import platform
import sympy as S
from sympy.functions.combinatorial.numbers import stirling

OUT = Path(__file__).resolve().parents[1] / "results"
X, a, L, M, u, v = S.symbols("X a L M u v")


@lru_cache(None)
def q_poly(N):
    return S.Poly(S.prod(X + a - j for j in range(1, N)) / S.factorial(N - 1), X)


def q_coeff(N, j, parameter=a):
    return q_poly(N).nth(j).subs(a, parameter)


def sinc_coefficient(j):
    return S.Integer(1) if j == 0 else 2 * (1 - S.Rational(2)**(1 - 2*j)) * S.zeta(2*j)


def cancelled_product(s, r):
    """Exact value of (s)_r zeta(s+r) at an integer s, r >= 1."""
    if s + r == 1:
        return (-1)**(r - 1) * S.factorial(r - 1)
    return S.rf(s, r) * S.zeta(s + r)


@lru_cache(None)
def base_integer_moment(h, s):
    return S.expand(-S.factorial(h) * sum(
        sinc_coefficient(j) * cancelled_product(s, h + 1 - 2*j)
        / S.factorial(h + 1 - 2*j) for j in range(h//2 + 1)))


def mellin_integer_moment(N, m, s, h):
    return S.expand((-1)**(N + m - 1) * sum(
        S.binomial(h, t) * S.diff(q_coeff(N, j), a, t).subs(a, m)
        * base_integer_moment(h-t, s-j)
        for j in range(N) for t in range(h+1)))


@lru_cache(None)
def beta_log_moment(A, B, h):
    """d_a^h B(a+k+1,N-a), with A,B positive integers."""
    beta = S.factorial(A-1) * S.factorial(B-1) / S.factorial(A+B-1)
    cumulants = [S.Integer(0)]
    for j in range(1, h+1):
        cumulants.append(S.expand_func(
            S.polygamma(j-1, A) + (-1)**j*S.polygamma(j-1, B)))
    bell = [S.Integer(1)]
    for n in range(h):
        bell.append(S.expand(sum(S.binomial(n,j)*bell[n-j]*cumulants[j+1]
                                 for j in range(n+1))))
    return S.expand(beta*bell[h])


def rational_polylog_moment(N, m, r, h):
    return S.expand(sum((-1)**(k+1)*S.factorial(k)*stirling(r+1,k+1,kind=2)
                        * beta_log_moment(m+k+1,N-m,h) for k in range(r+1)))


def scale_polynomials(n, r):
    p = S.Poly(S.prod(1-u/S.Integer(j) for j in range(1,r+1)),u)
    h = -S.factorial(n)*p.nth(n+1)
    c = S.expand(S.factorial(n)*sum(p.nth(j)*L**(n+1-j)/S.factorial(n+1-j)
                                  for j in range(min(n,r)+1)))
    b = S.expand(h+L**(n+1)/S.Integer(n+1)-c)
    return h,c,b


def closure_polynomials(max_degree):
    """Homogeneous gamma ratios, with formal Z_j denoting zeta(j)."""
    pieces=[S.Integer(1),S.Integer(0)]
    logs={j:S.Symbol(f"Z{j}")/j*((-1)**j*((u+v)**j-u**j)+v**j)
          for j in range(2,max_degree+1)}
    for d in range(2,max_degree+1):
        pieces.append(S.expand(sum(j*logs[j]*pieces[d-j] for j in range(2,d+1))/d))
    return pieces


def closure_row(m,n,pieces):
    N=m+n+1
    f=(-1)**(m+n)*S.factorial(m)*S.factorial(n)
    swap=lambda expr:expr.xreplace({u:v,v:u})
    coeff=lambda expr:S.Poly(S.expand(expr),u,v).coeff_monomial(u**(m+1)*v**(n+1))
    constant=-f*coeff(S.cancel((u*pieces[N+1]+v*swap(pieces[N+1]))/(u+v)))
    ca=[S.expand(-f*(-1)**j/S.factorial(j)*coeff(v*swap(pieces[N-j])*(u+v)**j))
        for j in range(N+1)]
    cb=[S.expand(-f*(-1)**j/S.factorial(j)*coeff(u*pieces[N-j]*(u+v)**j))
        for j in range(N+1)]
    return constant,ca,cb


def main():
    OUT.mkdir(exist_ok=True)
    counts={"coefficient_recurrence":0,"annihilation":0,"determinant":0,
            "rational_polylog_log_moments":0,"scale_composition":0,
            "scale_contact":0,"closure_invariants":0}
    tables=[]
    for N in range(1,9):
        mat=S.Matrix([[q_coeff(N,j,m) for j in range(N)] for m in range(N)])
        expected=(-1)**(N*(N-1)//2)/S.prod(S.factorial(j) for j in range(N))
        assert S.simplify(mat.det()-expected)==0
        counts["determinant"]+=1
        assert S.expand(q_poly(N+1).as_expr()-(X+a-N)*q_poly(N).as_expr()/N)==0
        counts["coefficient_recurrence"]+=1
        for k in range(N-1):
            assert S.expand(q_poly(N).as_expr().subs(X,k+1-a))==0
            counts["annihilation"]+=1
        tables.append({"N":N,"polynomial":str(q_poly(N).as_expr()),
                       "integer_table":[[str(x) for x in mat.row(m)] for m in range(N)],
                       "determinant":str(expected)})
    for N in range(1,7):
        for m in range(N):
            for r in range(5):
                for h in range(5):
                    left=mellin_integer_moment(N,m,-r,h)
                    right=rational_polylog_moment(N,m,r,h)
                    assert S.expand(left-right)==0,(N,m,r,h,left,right)
                    counts["rational_polylog_log_moments"]+=1
    scales=[]
    for r in range(6):
        for n in range(7):
            h,c,b=scale_polynomials(n,r)
            cc=scale_polynomials(n,r)[1].subs(L,M)
            cc+=sum(S.binomial(n,j)*M**(n-j)*scale_polynomials(j,r)[1] for j in range(n+1))
            bb=sum(S.binomial(n,j)*M**(n-j)*scale_polynomials(j,r)[2] for j in range(n+1))
            assert S.expand(c.subs(L,L+M)-cc)==0
            assert S.expand(b.subs(L,L+M)-bb)==0
            counts["scale_composition"]+=2
            expected_b=sum(S.binomial(n,j)*L**(n-j)*scale_polynomials(j,r)[0] for j in range(n+1))
            assert S.expand(b-expected_b)==0
            counts["scale_contact"]+=1
            scales.append({"n":n,"r":r,"h":str(h),"c":str(c),"b":str(b)})
    pieces=closure_polynomials(6)
    closures=[]
    for total in range(5):
        for m in range(total+1):
            n=total-m
            e,ca,cb=closure_row(m,n,pieces)
            er,car,cbr=closure_row(n,m,pieces)
            assert e==er and ca==cbr and cb==car
            assert ca[-1]==S.Rational(1,m+1) and cb[-1]==S.Rational(1,n+1)
            assert ca[-2]==cb[-2]==0
            counts["closure_invariants"]+=3
            closures.append({"m":m,"n":n,"constant":str(e),
                             "gamma_at_t":[str(x) for x in ca],"gamma_at_1_minus_t":[str(x) for x in cb]})
    e,ca,cb=closure_row(0,0,pieces)
    assert e==-2*S.Symbol('Z2') and ca==cb==[0,1]
    e,ca,cb=closure_row(1,0,pieces)
    assert e==-S.Symbol('Z3') and ca==[S.Symbol('Z2'),0,S.Rational(1,2)] and cb==[S.Symbol('Z2'),0,1]
    counts["closure_invariants"]+=2
    result={"status":"passed","python":platform.python_version(),"sympy":S.__version__,
            "counts":counts,"total_checks":sum(counts.values()),
            "meaning":"Exact finite algebra; the arbitrary-order theorems have analytic proofs in the article."}
    (OUT/"exact_verification.json").write_text(json.dumps(result,indent=2)+"\n")
    (OUT/"exact_coefficient_tables.json").write_text(json.dumps({"mellin":tables,"scale":scales,
        "undilated_closure":closures,"notation":"Z_j means zeta(j); gamma arrays are ordered by Stieltjes index."},indent=2)+"\n")
    print(json.dumps(result,indent=2))


if __name__=="__main__":
    main()
