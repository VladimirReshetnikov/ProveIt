"""Exact coefficient-only sextic resolvents.  No root approximation is used.

The decision entry point is restricted to irreducible degree-six polynomials
in QQ[x].  The coefficient identities themselves also hold at singular and
nonseparable inputs.  Python 3.10+; SymPy 1.14.0.
"""
from __future__ import annotations
from itertools import combinations
from typing import Sequence
import sympy as sp

X, Z = sp.symbols('x Z')


def monic_sextic(f: sp.Poly | sp.Expr) -> sp.Poly:
    p = sp.Poly(f, X, domain=sp.QQ)
    if p.degree() != 6:
        raise ValueError('Expected a degree-six polynomial in x over QQ.')
    return p.monic()


def companion(f: sp.Poly | sp.Expr) -> sp.Matrix:
    p = monic_sextic(f)
    C = sp.zeros(6)
    for j in range(5):
        C[j + 1, j] = 1
    coeff = list(reversed(p.all_coeffs()[1:]))
    for i, c in enumerate(coeff):
        C[i, 5] = -c
    return C


def wedge_matrix(C: sp.Matrix, k: int) -> sp.Matrix:
    """Multiplicative compound, ordered lexicographically by subsets."""
    if C.rows != C.cols or not 0 <= k <= C.rows:
        raise ValueError('Invalid square matrix / exterior degree.')
    basis = list(combinations(range(C.rows), k))
    return sp.Matrix([[C.extract(I, J).det() for J in basis] for I in basis])


def additive_compound(C: sp.Matrix, k: int) -> sp.Matrix:
    """Induced Lie-algebra action on the kth exterior power."""
    n = C.rows
    if n != C.cols or not 0 <= k <= n:
        raise ValueError('Invalid square matrix / exterior degree.')
    basis = list(combinations(range(n), k))
    index = {I: i for i, I in enumerate(basis)}
    A = sp.zeros(len(basis))
    for j, J in enumerate(basis):
        for q in range(k):
            for r in range(n):
                if C[r, J[q]] == 0:
                    continue
                I = list(J)
                I[q] = r
                if len(set(I)) != k:
                    continue
                inv = sum(I[a] > I[b] for a in range(k) for b in range(a+1, k))
                A[index[tuple(sorted(I))], j] += (-1)**inv * C[r, J[q]]
    return A


def newton_polynomial(power_sums: Sequence[sp.Expr], variable=Z) -> sp.Poly:
    coeff = [sp.S.One]
    for k in range(1, len(power_sums) + 1):
        coeff.append(-sum(coeff[k-i] * power_sums[i-1]
                          for i in range(1, k+1)) / k)
    return sp.Poly.from_list(coeff, variable, domain=sp.QQ)


def matching_resolvent(f: sp.Poly | sp.Expr) -> sp.Poly:
    """Product (Z - sum of the three pair products), degree 15."""
    p = monic_sextic(f)
    C = companion(p)
    S, P = additive_compound(C, 2), wedge_matrix(C, 2)
    I = sp.eye(15)
    e = [(-1)**j * p.nth(6-j) for j in range(7)]
    E = [I]
    for j in range(1, 5):
        E.append(e[j]*I - S*E[j-1] - (P*E[j-2] if j >= 2 else sp.zeros(15)))
    Q = E[1]*E[3] - 4*E[4]
    R = E[1]**2*E[4] + E[3]**2 - 4*E[2]*E[4]
    L1 = -3*P - E[2]
    L2 = 3*P**2 + 2*E[2]*P + Q
    L3 = -P**3 - E[2]*P**2 - Q*P - R
    W = [3*I, -L1]
    W.append(-L1*W[1] - 2*L2)
    W.append(-L1*W[2] - L2*W[1] - 3*L3)
    for k in range(4, 16):
        W.append(-L1*W[k-1] - L2*W[k-2] - L3*W[k-3])
    return newton_polynomial([sp.trace(W[k])/3 for k in range(1, 16)])


def middle_pairing(n: int = 6) -> sp.Matrix:
    if n % 2 != 0 or (n//2) % 2 != 1:
        raise ValueError('The middle exterior degree must be odd.')
    k = n//2
    basis = list(combinations(range(n), k))
    index = {I: i for i, I in enumerate(basis)}
    J = sp.zeros(len(basis))
    for i, I in enumerate(basis):
        K = tuple(r for r in range(n) if r not in I)
        seq = I + K
        inv = sum(seq[a] > seq[b] for a in range(n) for b in range(a+1, n))
        J[i, index[K]] = (-1)**inv
    return J


def triple_operator(f: sp.Poly | sp.Expr) -> tuple[sp.Matrix, sp.Matrix]:
    D = wedge_matrix(companion(f), 3)
    J = middle_pairing()
    return J, D - J*D.T*J  # J^{-1} = -J


def pfaffian(A: sp.Matrix) -> sp.Expr:
    """Exact skew Gaussian elimination, including singular matrices.

    This arithmetic routine uses rational divisions; the Pfaffian function
    and the article's matrix formula are polynomials without denominators.
    """
    A = sp.Matrix(A)
    n = A.rows
    if n != A.cols or n % 2 or A.T != -A:
        raise ValueError('Expected an even-size skew-symmetric matrix.')
    result = sp.S.One
    for k in range(0, n, 2):
        pivot = next((j for j in range(k+1, n) if A[k, j] != 0), None)
        if pivot is None:
            return sp.S.Zero
        if pivot != k+1:
            A.row_swap(k+1, pivot)
            A.col_swap(k+1, pivot)
            result = -result
        a = A[k, k+1]
        result *= a
        for i in range(k+2, n):
            for j in range(i+1, n):
                val = A[i, j] - (A[k, i]*A[k+1, j] - A[k, j]*A[k+1, i])/a
                A[i, j], A[j, i] = val, -val
    return sp.cancel(result)


def triple_resolvent(f: sp.Poly | sp.Expr, *, method: str = 'trace') -> sp.Poly:
    """Product (Z - product(first triple) - product(second triple))."""
    J, H = triple_operator(f)
    if method == 'trace':
        power, sums = sp.eye(20), []
        for _ in range(10):
            power = power*H
            sums.append(sp.trace(power)/2)
        return newton_polynomial(sums)
    if method == 'pfaffian':
        sign = pfaffian(J)
        points = [(i, pfaffian(J*(i*sp.eye(20)-H))/sign) for i in range(11)]
        return sp.Poly(sp.interpolate(points, Z), Z, domain=sp.QQ)
    raise ValueError("method must be 'trace' or 'pfaffian'")


def zero_matching_resolvent(f: sp.Poly | sp.Expr) -> sp.Poly:
    """The repository's R_2(0,Z) = product (Z + C_P)."""
    p = monic_sextic(f)
    e6 = p.nth(0)
    if e6 == 0:
        raise ValueError('Reciprocal implementation requires nonzero constant term.')
    reciprocal = sp.Poly.from_list(list(reversed(p.all_coeffs())), X, domain=sp.QQ).monic()
    m = matching_resolvent(reciprocal)
    return sp.Poly(sp.expand((-e6)**15 * m.as_expr().subs(Z, -Z/e6)), Z, domain=sp.QQ)


def rational_roots(p: sp.Poly) -> dict[sp.Expr, int]:
    """Extract all rational roots with multiplicities by exact factorization."""
    roots: dict[sp.Expr, int] = {}
    for q, multiplicity in sp.factor_list(p)[1]:
        if q.degree() == 1:
            roots[-q.nth(0)/q.nth(1)] = multiplicity
    return roots


def decide_irreducible_sextic(f: sp.Poly | sp.Expr) -> bool:
    """Decide radical solvability over QQ; reducible inputs are rejected."""
    p = monic_sextic(f)
    if not p.is_irreducible:
        raise ValueError('The two-resolvent criterion requires irreducibility.')
    if rational_roots(matching_resolvent(p)):
        return True
    return bool(rational_roots(triple_resolvent(p)))


if __name__ == '__main__':
    import argparse, json
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('coefficients', nargs=7, type=sp.Rational,
                        help='Seven rational coefficients, highest degree first.')
    args = parser.parse_args()
    try:
        f = sp.Poly.from_list(args.coefficients, X, domain=sp.QQ)
        solvable = decide_irreducible_sextic(f)
    except (ValueError, sp.PolynomialError) as exc:
        parser.error(str(exc))
    print(json.dumps({'polynomial': str(f.as_expr()),
                      'solvable': solvable}, indent=2))
