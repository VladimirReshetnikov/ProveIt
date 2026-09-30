"""Exact coefficient-only block resolvents for an irreducible rational sextic.

Requires Python >= 3.10 and SymPy >= 1.14 (tested with 1.14.0).
No numerical roots, splitting-field construction, or separating-parameter search.
The main interface is decide_irreducible_sextic(poly, variable).
"""
from __future__ import annotations
from itertools import combinations
from typing import Sequence
import sympy as sp


def companion(poly: sp.Poly) -> sp.Matrix:
    """Multiplication by X in the power basis of Q[X]/(poly)."""
    if not poly.is_monic:
        raise ValueError("The companion input must be monic.")
    n = poly.degree()
    C = sp.zeros(n)
    for i in range(n - 1):
        C[i + 1, i] = 1
    for i in range(n):
        C[i, n - 1] = -poly.nth(i)
    return C


def compound(C: sp.Matrix, k: int) -> sp.Matrix:
    """Multiplicative compound: matrix of the induced map on exterior power k."""
    n = C.rows
    if C.cols != n or not 0 <= k <= n:
        raise ValueError("A square matrix and 0 <= k <= n are required.")
    basis = list(combinations(range(n), k))
    return sp.Matrix([[C.extract(I, J).det() for J in basis] for I in basis])


def additive_compound(C: sp.Matrix, k: int) -> sp.Matrix:
    """Derivative at u=0 of exterior_power(I+u*C), without differentiation."""
    n = C.rows
    basis = list(combinations(range(n), k))
    index = {I: i for i, I in enumerate(basis)}
    S = sp.zeros(len(basis))
    for col, J in enumerate(basis):
        for r in range(k):
            for i in range(n):
                if C[i, J[r]] == 0:
                    continue
                K = list(J)
                K[r] = i
                if len(set(K)) < k:
                    continue
                inversions = sum(K[a] > K[b] for a in range(k) for b in range(a + 1, k))
                row = index[tuple(sorted(K))]
                S[row, col] += (-1) ** inversions * C[i, J[r]]
    return S


def monic_power_root(poly: sp.Poly, power: int) -> sp.Poly:
    """Recover the unique monic Q with Q**power == poly, then verify exactly.

    Uses descending coefficients, not factorization. Raises on a failed identity.
    """
    if power < 1 or not poly.is_monic or poly.degree() % power:
        raise ValueError("Expected a monic polynomial of degree divisible by power.")
    d = poly.degree() // power
    q = [sp.S.One]
    for k in range(1, d + 1):
        acc = [sp.S.One]
        for _ in range(power):
            nxt = [sp.S.Zero] * (min(k, len(acc) + len(q) - 2) + 1)
            for i, a in enumerate(acc):
                for j, b in enumerate(q):
                    if i + j <= k:
                        nxt[i + j] += a * b
            acc = nxt
        known = acc[k] if k < len(acc) else sp.S.Zero
        q.append((poly.nth(poly.degree() - k) - known) / power)
    z = poly.gen
    result = sp.Poly.from_list(q, z, domain=sp.QQ)
    if result ** power != poly:
        raise ArithmeticError("The expected perfect-power identity did not hold.")
    return result


class SexticResolvents:
    """Build the compressed pair (degree 15) and triple (degree 10) resolvents.

    The matrix identities also hold for any separable monic sextic. Irreducibility
    is checked by the decision function, rather than by this constructor.
    """
    def __init__(self, poly: sp.Poly | sp.Expr, x: sp.Symbol):
        self.f = sp.Poly(poly, x, domain=sp.QQ).monic()
        if self.f.degree() != 6:
            raise ValueError("A sextic polynomial is required.")
        if sp.gcd(self.f, self.f.diff()).degree() != 0:
            raise ValueError("The sextic must be separable.")
        self.x = x
        self.C = companion(self.f)
        self.e = [sp.S.One] + [(-1) ** i * self.f.nth(6 - i) for i in range(1, 7)]
        self.I = sp.eye(15)
        self.S = additive_compound(self.C, 2)
        self.P = compound(self.C, 2)
        I, S, P, e = self.I, self.S, self.P, self.e
        self.r1 = e[1] * I - S
        self.r2 = e[2] * I - P - S * self.r1
        self.r3 = e[3] * I - P * self.r1 - S * self.r2
        self.r4 = e[4] * I - P * self.r2 - S * self.r3
        self.U = self.r1 * self.r3 - 4 * self.r4
        self.V = self.r3 ** 2 + self.r1 ** 2 * self.r4 - 4 * self.r2 * self.r4

    def pair(self, t: sp.Rational | int, z: sp.Symbol | None = None) -> sp.Poly:
        """R_2(t,z) from a 45-by-45 rational block companion matrix."""
        t = sp.Rational(t)
        z = z if z is not None else sp.Symbol('z')
        I, S, P = self.I, self.S, self.P
        q = t ** 2 * I + t * S - P
        H = t ** 2 * P + t * (self.r3 + P * self.r1) - self.r4
        N2 = -3 * H - self.r2 * q
        N1 = 3 * H ** 2 + 2 * self.r2 * q * H + self.U * q ** 2
        N0 = -H ** 3 - self.r2 * q * H ** 2 - self.U * q ** 2 * H - self.V * q ** 3
        O = sp.zeros(15)
        block = sp.BlockMatrix([[O, O, -N0], [I, O, -N1], [O, I, -N2]]).as_explicit()
        cubed = sp.Poly(block.charpoly(z).as_expr(), z, domain=sp.QQ)
        return monic_power_root(cubed, 3)

    def triple(self, t: sp.Rational | int, z: sp.Symbol | None = None) -> sp.Poly:
        """R_3(t,z) from a 20-by-20 rational matrix; requires f(t) != 0."""
        t = sp.Rational(t)
        z = z if z is not None else sp.Symbol('z')
        value = self.f.eval(t)
        if value == 0:
            raise ValueError("The triple matrix formula requires f(t) != 0.")
        D = compound(t * sp.eye(6) - self.C, 3)
        M = D + value * D.inv() - (2 * t ** 3 - self.e[1] * t ** 2) * sp.eye(20)
        squared = sp.Poly(M.charpoly(z).as_expr(), z, domain=sp.QQ)
        return monic_power_root(squared, 2)


def rational_roots(poly: sp.Poly) -> dict:
    """Exact rational roots with their multiplicities (no numerical recognition)."""
    return poly.ground_roots()


def decide_irreducible_sextic(
    poly: sp.Poly | sp.Expr,
    x: sp.Symbol,
    pair_tests: Sequence[sp.Rational | int] = (1, 2, 3),
    triple_test: sp.Rational | int = 1,
) -> dict:
    """Decide solvability by radicals of an irreducible sextic over Q.

    The return value records the exact rational-root evidence used. Repeated
    resolvent roots are allowed. No Galois-group routine is called here.
    """
    f = sp.Poly(poly, x, domain=sp.QQ).monic()
    if f.degree() != 6 or not f.is_irreducible:
        raise ValueError("Input must be an irreducible rational sextic.")
    tests = tuple(sp.Rational(t) for t in pair_tests)
    if len(tests) != 3 or len(set(tests)) != 3 or 0 in tests:
        raise ValueError("Use three distinct nonzero rational pair test values.")
    triple_test = sp.Rational(triple_test)
    if triple_test == 0:
        raise ValueError("Use a nonzero rational triple test value.")
    builder = SexticResolvents(f, x)
    r3 = rational_roots(builder.triple(triple_test))
    evidence = {"triple": {"t": str(triple_test), "roots": {str(a): int(m) for a, m in r3.items()}}, "pairs": []}
    if r3:
        return {"solvable": True, "reason": "triple resolvent has a rational root", "evidence": evidence}
    for t in tests:
        r2 = rational_roots(builder.pair(t))
        evidence["pairs"].append({"t": str(t), "roots": {str(a): int(m) for a, m in r2.items()}})
        if not r2:
            return {"solvable": False, "reason": "one pair test and the triple test have no rational root", "evidence": evidence}
    return {"solvable": True, "reason": "all three pair tests have rational roots", "evidence": evidence}


if __name__ == '__main__':
    import argparse, json
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('polynomial', help='A trusted local SymPy expression in x, e.g. x**6+x+1')
    args = parser.parse_args()
    x = sp.Symbol('x')
    # sympify is a local convenience parser, not a sandbox for untrusted input.
    result = decide_irreducible_sextic(sp.sympify(args.polynomial, locals={'x': x}), x)
    print(json.dumps(result, indent=2))
