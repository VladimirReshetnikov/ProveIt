#!/usr/bin/env python3
"""Exact finite-jet checks for the Puiseux/iPRA report.

Python 3.10+, standard library only.  This is an executable illustration and
certificate checker, not a formalization of iPRA and not a general Puiseux solver.
All coefficients are Gaussian rationals; every equality checked is exact.
"""
from __future__ import annotations
from dataclasses import dataclass
from fractions import Fraction as Q
from pathlib import Path
import argparse
import json


@dataclass(frozen=True)
class G:
    re: Q = Q(0)
    im: Q = Q(0)

    def __post_init__(self):
        object.__setattr__(self, "re", Q(self.re))
        object.__setattr__(self, "im", Q(self.im))

    def __add__(self, other):
        b = g(other)
        return G(self.re + b.re, self.im + b.im)

    __radd__ = __add__

    def __neg__(self):
        return G(-self.re, -self.im)

    def __sub__(self, other):
        return self + (-g(other))

    def __rsub__(self, other):
        return g(other) + (-self)

    def __mul__(self, other):
        b = g(other)
        return G(self.re*b.re - self.im*b.im,
                 self.re*b.im + self.im*b.re)

    __rmul__ = __mul__

    def inv(self):
        n = self.re*self.re + self.im*self.im
        if not n:
            raise ZeroDivisionError
        return G(self.re/n, -self.im/n)

    def __truediv__(self, other):
        return self * g(other).inv()

    def __bool__(self):
        return bool(self.re or self.im)

    def bound(self):
        """Rational upper bound for complex modulus."""
        return abs(self.re) + abs(self.im)

    def data(self):
        return [str(self.re), str(self.im)]


def g(x):
    return x if isinstance(x, G) else G(x)


ZERO, ONE, I = G(), G(1), G(0, 1)
# Bivariate polynomials in (T,U), represented by exponent-pair dictionaries.
Poly = dict[tuple[int, int], G]


def clean(p):
    return {ij: g(a) for ij, a in p.items() if g(a)}


def add(p, q):
    r = dict(p)
    for ij, a in q.items():
        r[ij] = r.get(ij, ZERO) + a
    return clean(r)


def scale(p, a):
    return clean({ij: g(a)*c for ij, c in p.items()})


def mul(p, q):
    r = {}
    for (i, j), a in p.items():
        for (k, l), b in q.items():
            ij = (i+k, j+l)
            r[ij] = r.get(ij, ZERO) + a*b
    return clean(r)


def power(p, n):
    r = {(0, 0): ONE}
    for _ in range(n):
        r = mul(r, p)
    return r


T, U = {(1, 0): ONE}, {(0, 1): ONE}
C = lambda a: clean({(0, 0): g(a)})


def shifted(p, c):
    """Replace U by c+U."""
    r = {}
    for (i, j), a in p.items():
        r = add(r, mul({(i, 0): a}, power(add(C(c), U), j)))
    return r


def smul(a, b, n):
    r = [ZERO] * (n+1)
    for i, ai in enumerate(a[:n+1]):
        if ai:
            for j, bj in enumerate(b[:n+1-i]):
                if bj:
                    r[i+j] = r[i+j] + ai*bj
    return r


def seval(p, u, n):
    powers = [[ONE] + [ZERO]*n]
    for _ in range(max((j for i, j in p), default=0)):
        powers.append(smul(powers[-1], u, n))
    out = [ZERO]*(n+1)
    for (i, j), a in p.items():
        if i <= n:
            for k in range(n+1-i):
                out[i+k] = out[i+k] + a*powers[j][k]
    return out


def implicit(h, n):
    """Unique zero-constant solution H(T,U)=0 through degree n."""
    assert not h.get((0, 0), ZERO)
    d = h.get((0, 1), ZERO)
    assert d
    phi = add(U, scale(h, -d.inv()))
    assert not phi.get((0, 0), ZERO)
    assert not phi.get((0, 1), ZERO)
    u = [ZERO]*(n+1)
    for k in range(1, n+1):
        u[k] = seval(phi, u[:k] + [ZERO], k)[k]
    assert not any(seval(h, u, n))
    S = Q(1) + sum((j+1)*a.bound() for (i, j), a in phi.items())
    r, rho = 1/(4*S), 1/(16*S*S)
    # Stronger l1 coordinate norm bounds the Euclidean complex modulus.
    weighted = sum(u[k].bound()*rho**k for k in range(1, n+1))
    assert weighted <= r
    return u, {"S": str(S), "r": str(r), "rho": str(rho),
               "weighted_l1_sum": str(weighted)}


def laurent_mul(a, b, lo, hi):
    out = {}
    for i, ai in a.items():
        for j, bj in b.items():
            k = i+j
            if lo <= k <= hi:
                out[k] = out.get(k, ZERO) + ai*bj
    return {k: a for k, a in out.items() if a}


def product_linear(roots, multiplicities, cutoff, pole):
    """Y-coefficient arrays; retains extra high orders needed by later poles."""
    out = [{0: ONE}]
    total = sum(multiplicities)
    for root, mult in zip(roots, multiplicities):
        for _ in range(mult):
            new = [{} for _ in range(len(out)+1)]
            for j, coeff in enumerate(out):
                prod = laurent_mul(coeff, root, -total*pole,
                                   cutoff + total*pole)
                for k, a in prod.items():
                    new[j][k] = new[j].get(k, ZERO) - a
                for k, a in coeff.items():
                    new[j+1][k] = new[j+1].get(k, ZERO) + a
            out = new
    return [{k: a for k, a in p.items() if a and k <= cutoff}
            for p in out]


def expected_product(p, ramification, scalar_exp, cutoff):
    """P(T^e,Y)/T^scalar_exp; examples have monomial leading coefficient."""
    n = max(j for i, j in p)
    out = [{} for _ in range(n+1)]
    for (i, j), a in p.items():
        k = ramification*i - scalar_exp
        if k <= cutoff:
            out[j][k] = out[j].get(k, ZERO) + a
    return [{k: a for k, a in row.items() if a} for row in out]


def sparse(a, start=0):
    return {start+k: c for k, c in enumerate(a) if c}


def run(cutoff):
    records = []

    def verify(name, p, e, roots, mult, pole=0, scalar=0, bounds=None):
        actual = product_linear(roots, mult, cutoff, pole)
        expected = expected_product(p, e, scalar, cutoff)
        assert actual == expected, (name, actual, expected)
        records.append({
            "name": name, "ramification": e, "multiplicities": mult,
            "verified_t_degree": cutoff,
            "identity": "P(T^e,Y) / T^scalar = product (Y-root)^multiplicity",
            "scalar_exponent": scalar,
            "first_nonzero_terms": [
                [[k, a.data()] for k, a in sorted(row.items())[:8]]
                for row in roots],
            "majorant_certificates": bounds or [],
        })

    # Cusp, including the finite polynomial endpoint of the recurrence.
    p = add(power(U, 2), scale(power(T, 3), -1))
    verify("cusp", p, 2, [{3: ONE}, {3: -ONE}], [1, 1])

    # Genuine fourth-root ramification with a repeated first Newton face.
    p = add(power(add(power(U, 2), scale(power(T, 3), -1)), 2),
            scale(mul(power(T, 7), U), -1))
    roots, bounds = [], []
    for s, c in [(1, G(Q(1, 2))), (1, G(Q(-1, 2))),
                 (-1, G(0, Q(1, 2))), (-1, G(0, Q(-1, 2)))]:
        # H(T,Z)=(2Z+T^5 Z^2)^2-s(1+T^5 Z).
        h = add(power(add(scale(U, 2), mul(power(T, 5), power(U, 2))), 2),
                scale(add(C(1), mul(power(T, 5), U)), -s))
        z, cert = implicit(shifted(h, c), cutoff)
        z[0] = c
        y = {6: g(s)}
        y.update({11+k: g(s)*v for k, v in enumerate(z) if v})
        roots.append(y)
        bounds.append(cert)
    verify("ramification_four", p, 4, roots, [1]*4, bounds=bounds)

    # Repeated factors: multiplicity is retained and never inferred numerically.
    p = mul(power(add(power(U, 2), scale(power(T, 3), -1)), 3),
            add(U, scale(power(T, 2), -1)))
    verify("repeated_factors", p, 2,
           [{3: ONE}, {3: -ONE}, {4: ONE}], [3, 3, 1])

    # A pair of Laurent branches; extra terms protect the product from poles.
    p = add(mul(T, power(U, 2)), scale(add(C(1), T), -1))
    roots, bounds = [], []
    for c in [ONE, -ONE]:
        h = add(power(U, 2), scale(add(C(1), power(T, 2)), -1))
        z, cert = implicit(shifted(h, c), cutoff+8)
        z[0] = c
        roots.append(sparse(z, -1))
        bounds.append(cert)
    verify("pole", p, 2, roots, [1, 1], pole=1, scalar=2, bounds=bounds)

    # Degree two does not bound the singularity order.
    p = add(power(add(U, scale(power(T, 20), -1)), 2),
            scale(power(T, 41), -1))
    verify("high_contact", p, 2,
           [{40: ONE, 41: ONE}, {40: ONE, 41: -ONE}], [1, 1])

    return {"arithmetic": "exact Gaussian rationals (fractions.Fraction)",
            "status": "all finite checks passed",
            "limitations": [
                "Not a general Newton-Puiseux implementation.",
                "Not a Lean or iPRA proof.",
                "Finite examples do not establish the universal theorem."],
            "examples": records}


if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("--cutoff", type=int, default=96)
    ap.add_argument("--output", type=Path)
    args = ap.parse_args()
    if args.cutoff < 84:
        ap.error("cutoff must be at least 84 to exercise the high-contact case")
    result = run(args.cutoff)
    if args.output:
        args.output.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps({"status": result["status"],
                      "examples": len(result["examples"]),
                      "cutoff": args.cutoff,
                      "checks": ["implicit recurrences", "weighted majorants",
                                 "full products with multiplicities",
                                 "Laurent pole bookkeeping"]}, indent=2))
