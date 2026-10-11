#!/usr/bin/env python3
"""Exact checks for the all-orders p=4 optimal-prefix proof.

The proof is in sections/03c_moment_rank_four.tex.  This certificate verifies both
symbolic identities with indeterminate b,u,v,w and finite-order source
matrices, keeping these two kinds of evidence explicitly distinct.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path

import sympy as sp


def mu(n):
    return sp.S.Zero if n < 0 else sp.bernoulli(2 * n) / sp.factorial(2 * n)


def c(n):
    return (2 * n + 1) * sp.factorial(2 * n + 2) / sp.factorial(4 * n + 2)


def r(n):
    return sp.Rational(1, 6) * (2*n-1) * (2*n) * (2*n+3) * (2*n+4)


def pi_coeff(n, t):
    if t > n:
        return sp.S.Zero
    ell = n - t
    return (2 * sp.factorial(4*n+1-2*ell) * sp.factorial(2*n+1)
            / (sp.factorial(4*n+2) * sp.factorial(2*ell+1)
               * sp.factorial(2*n-2*ell)))


def xi(b, u, v, w):
    d = 4*b*b - 6*b - 1
    return (4*d + (b-2)*(2*b-5)*(u+(2*b-1)*w*(4-u))
            + (b-1)*(2*b-3)*((2*b-1)*v*v-4*(b+1)*v))


def contractions(b, u, v, w):
    rm, rp = r(b-2), r(b-1)
    sm0, sm1 = rm*(1-u/2), 1-v
    sp0 = (rp - (2*b-3)*(2*b-2)*(2*b-1)*(4*b-3)*v/3
           - (2*b-3)*(2*b-2)*(2*b-4)*(2*b-5)*u/12)
    sp1 = (1 - 2*(4*b-3)*w/b
           - (b-1)*(2*b-3)*v/(b*(2*b-1)))
    return sp.Matrix([[sp0, sp1], [sm0, sm1]])


def symbolic_checks():
    b, u, v, w = sp.symbols("b u v w")
    rp, rm = r(b-1), r(b-2)
    d = 4*b*b-6*b-1
    assert sp.factor(rp-rm-2*(4*b-3)*d/3) == 0
    S = contractions(b, u, v, w)
    k = sp.symbols("k")

    def cubic_sum(poly, N, B_Nm1, B_Nm3):
        return (N*poly.subs(k,1)/2
                + N*(poly.subs(k,N-1)-poly.subs(k,N))*B_Nm1
                - N*(N-1)*(N-2)*B_Nm3)

    reduced = sp.Matrix([
        [(2*b-2)*cubic_sum((k+3)*(k+2*b)*(k+2*b+1),
                           2*b-3, v, u)/12,
         cubic_sum((k+1)*(k+2*b-2)*(k+2*b-1),
                   2*b-1, w, v)/(2*b*(2*b-1)**2)],
        [(2*b)*(2*b-1)*(2*b-4)*(2*b-5)*(2-u)/12,
         1-v],
    ])
    assert all(sp.factor(entry) == 0 for entry in reduced-S)
    ratio = ((rp+S[0,0])*(1+S[1,1])
             - (rm+S[1,0])*(1+S[0,1]))/(rp-rm)
    assert sp.factor(ratio-xi(b,u,v,w)/d) == 0

    U,V,W = sp.symbols("U V W")
    four_xi = sp.expand(4*xi(b,U/2,V/2,W/2))
    displayed = (16*d+(b-2)*(2*b-5)*(2*U+(2*b-1)*W*(8-U))
                 +(b-1)*(2*b-3)*((2*b-1)*V*V-8*(b+1)*V))
    assert sp.expand(four_xi-displayed) == 0
    residue = sp.Poly(sp.expand(four_xi.subs({U:1,V:1,W:1})), b,
                      modulus=2)
    assert residue == sp.Poly(1,b,modulus=2)
    return {"two_by_two_determinant_identity": True,
            "four_weighted_Bernoulli_reductions": True,
            "delta_factorization": True,
            "all_parameter_parity_polynomial": str(residue.as_expr())}


def source_matrix(b):
    def entry(t,k):
        p,q,d = 4,2*b,2*(b+t)+1
        e = d-p-q+2*k+1
        if e < 0:
            return sp.S.Zero
        return sp.bernoulli(e)*sum(
            sp.binomial(upper,lower)/upper
            for upper,lower in [(d-q+1,p-2*k),(d-p+1,q-2*k)]
            if 2 <= lower <= upper)
    return sp.Matrix(b,b,entry)


def finite_check(b):
    M = source_matrix(b)
    H = sp.Matrix(b,b,lambda t,k:mu(t+k-1))
    rows = [sp.factorial(2*b+2*t-3) for t in range(b)]
    cols = [1/sp.factorial(2*b-2*k) for k in range(b)]
    U = sp.Matrix(b,b,lambda t,k:
        mu(t+k-1)*sp.factorial(2*t+1)*sp.factorial(2*b-2*k)
        /(sp.factorial(4-2*k)*sp.factorial(2*b+2*t-3))
        if k < 2 else 0)
    assert M == sp.diag(*rows)*(H+U)*sp.diag(*cols)

    rp,rm = r(b-1),r(b-2)
    delta = rp-rm
    pp = sp.Matrix([[pi_coeff(b-1,t)/c(b-1) for t in range(b)]])
    pm = sp.Matrix([[pi_coeff(b-2,t)/c(b-2) for t in range(b)]])
    V = sp.Matrix.vstack((pp-pm)/delta,(-rm*pp+rp*pm)/delta)
    assert V*H == sp.eye(b)[:2,:]
    S = sp.Matrix.vstack(pp*U[:,:2],pm*U[:,:2])
    d = 4*b*b-6*b-1
    baseline = -d/(6*sp.Integer(2)**b*(b-1)*sp.factorial(2*b-4))
    assert sp.prod(rows)*sp.prod(cols)*H.det() == baseline

    actual = sp.factor(M.det())
    if b == 3:
        assert actual == -sp.Rational(113,384)
        return {"b":b,"q":2*b,"determinant":str(actual),
                "case":"explicit exceptional case","all_checks_passed":True}

    u,v,w = [sp.bernoulli(j) for j in (2*b-6,2*b-4,2*b-2)]
    assert S == contractions(sp.Integer(b),u,v,w)
    Xi = sp.factor(xi(b,u,v,w))
    claimed = -Xi/(6*sp.Integer(2)**b*(b-1)*sp.factorial(2*b-4))
    assert actual == claimed
    assert sp.factor((H+U).det()/H.det()) == Xi/d
    numerator,denominator = map(int,sp.fraction(4*Xi))
    assert numerator%2 == 1 and denominator%2 == 1
    return {"b":b,"q":2*b,"determinant":str(actual),"Xi":str(Xi),
            "v2_Xi":-2,"all_checks_passed":True}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--max-b",type=int,default=12)
    parser.add_argument("--output",type=Path)
    args = parser.parse_args()
    if args.max_b < 3:
        raise SystemExit("--max-b must be at least 3")
    result = {"proof":"sections/03c_moment_rank_four.tex (all orders)",
              "symbolic_parameter_checks":symbolic_checks(),
              "finite_source_matrix_checks":[finite_check(b)
                                             for b in range(3,args.max_b+1)]}
    output = json.dumps(result,indent=2)+"\n"
    if args.output:
        args.output.write_text(output)
    print(output)


if __name__ == "__main__":
    main()
