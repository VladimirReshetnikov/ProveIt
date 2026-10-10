"""Exact integral diagonalization of the odd-weight shuffle minor.

No numerical periods are used.  SymPy is only an exact polynomial/matrix
engine.  The proof itself is the central-factorial identity documented in
sections/05_shuffle_and_identities.tex. Running this file writes
odd_inner_certificate.json beside the script.
"""
from __future__ import annotations
from fractions import Fraction
from functools import reduce
from math import comb, gcd, lcm, prod
from pathlib import Path
import json
import sympy as s
from sympy.matrices.normalforms import smith_normal_form
from sympy.polys.domains import ZZ

BASE = Path(__file__).resolve().parent
y, t = s.symbols("y t")


def binomial(n, k):
    return comb(n, k) if 0 <= k <= n else 0


def matrices(m):
    # p,k are zero based.  Column k is outer index 2k+1, inner 2m-2k.
    M = s.Matrix(m, m, lambda p, k:
                 binomial(2*k, p) + binomial(2*k, 2*m-1-p))
    B = s.Matrix(m, m, lambda p, j:
                 binomial(2*m-1-2*j, p-j))
    R = s.Matrix(m, m, lambda j, k: int(j+k == m-1))
    P = s.zeros(m)
    Q = s.zeros(m)
    E = s.zeros(m)
    # Power-sum polynomials E_n satisfy E_0=2,E_1=1,E_n=E_{n-1}-t E_{n-2}.
    Es = [s.Integer(2), s.Integer(1)]
    for n in range(2, 2*m):
        Es.append(s.expand(Es[-1]-t*Es[-2]))
    for j in range(m):
        p = s.Poly(y*prod(y*y-r*r for r in range(1, j+1)), y)
        q = s.Poly((-1)**j*prod(t+r*(r-1) for r in range(1, j+1)), t)
        e = s.Poly(Es[2*j+1], t)
        for h in range(m):
            P[h, j] = p.nth(2*h+1)
            Q[h, j] = q.nth(h)
            E[h, j] = e.nth(h)
        assert s.expand(p.as_expr()+p.as_expr().subs(y, 1-y)
                        -(2*j+1)*q.as_expr().subs(t, y*(1-y))) == 0
    D = s.diag(*range(1, 2*m, 2))
    assert E*P == Q*D
    assert M == B*E*R
    # Every entry of each displayed change of basis is an integer.
    U = (B*Q).inv()
    V = R*P
    assert all(c.q == 1 for c in U)
    assert all(c.q == 1 for c in V)
    assert abs(U.det()) == 1 and abs(V.det()) == 1
    assert U*M*V == D
    return M, U, V, D


def serialize_matrix(A):
    return [[str(A[i, j]) for j in range(A.cols)] for i in range(A.rows)]


def shuffle_matrix(m):
    w = 2*m+1
    # p=1,...,m, a=1,...,2m, coordinates F_{a,w-a}.
    return s.Matrix(m, 2*m, lambda p, a:
                    binomial(a, p)+binomial(a, 2*m-1-p))


def row_identity(m, coefficients):
    """Return an exact functional identity sum c_p Li_p Li_{w-p} = sum d_a F.

    Both sides are symbolic.  The caller may specialize to any common
    analytic domain, including the convergent Gaussian boundary.
    """
    A = shuffle_matrix(m)
    c = s.Matrix(1, m, coefficients)
    return list(c*A)


def run():
    records = []
    for m in range(1, 21):
        M, U, V, D = matrices(m)
        expected_det = prod(range(1, 2*m, 2))
        assert M.det() == expected_det
        denom = lcm(*(int(c.q) for c in M.inv()))
        optimal_denom = lcm(*range(1, 2*m, 2))
        assert denom == optimal_denom
        snf = smith_normal_form(M, domain=ZZ)
        ds = smith_normal_form(D, domain=ZZ)
        factors = [abs(int(snf[i, i])) for i in range(m)]
        assert factors == [abs(int(ds[i, i])) for i in range(m)]
        records.append({"m": m, "weight": 2*m+1,
                        "determinant": str(expected_det),
                        "smith_invariant_factors": [str(n) for n in factors],
                        "optimal_inverse_denominator": str(denom)})
    # Small enough to audit by hand; contains all exact matrices U M V = D.
    m = 5
    M, U, V, D = matrices(m)
    short_products = [0, -7, 14, -16, 8]
    short_doubles = [0, -7, 0, 5, 0, -7, 0, 35, 105, 210]
    assert row_identity(m, short_products) == short_doubles
    pi_coefficient = s.Integer(0)
    for p, c in enumerate(short_products, 1):
        if c == 0:
            continue
        q = 11-p
        even = p if p % 2 == 0 else q
        odd = 11-even
        beta_coefficient = s.Rational(abs(int(s.euler(odd-1))),
                                      4**((odd+1)//2)*s.factorial(odd-1))
        real_coefficient = s.Rational(1, 2**even)*(1-s.Rational(1, 2**(even-1)))
        pi_coefficient -= c*real_coefficient*s.zeta(even)/s.pi**even*beta_coefficient
    assert pi_coefficient == s.Rational(223339, 29727129600)
    # An explicit new weight-eleven functional identity: second minus fourth
    # row times a rational factor can be selected for simple term cancellation.
    # Store the five rows as the transparent complete certificate instead.
    out = {"status": "exact integral matrix and shuffle certificates",
           "scope": "formal identities; no numerical period-independence assertion",
           "tested_m": [1, 20], "results": records,
           "weight_eleven": {"M": serialize_matrix(M),
                              "U": serialize_matrix(U),
                              "V": serialize_matrix(V),
                              "D": serialize_matrix(D),
                              "shuffle_rows": serialize_matrix(shuffle_matrix(m)),
                              "short_product_coefficients": short_products,
                              "short_double_coefficients": short_doubles,
                              "short_Gaussian_pi_coefficient": str(pi_coefficient),
                              "double_coordinate_order": [[a, 11-a] for a in range(1, 11)],
                              "product_order": [[p, 11-p] for p in range(1, 6)]}}
    path = BASE / "odd_inner_certificate.json"
    path.write_text(json.dumps(out, indent=2)+"\n")
    print(f"PASS: U M V = diag(1,3,...,2m-1), determinant, Smith form and")
    print(f"optimal inverse denominators verified for 1 <= m <= 20; {path.name}")


if __name__ == "__main__":
    run()
