#!/usr/bin/env python3
"""Exact, independent checks for the elliptic Jacobi-fraction theorem.

Only Python's standard library is required. No floating-point arithmetic is used.
Run: python verify.py --output data
The mathematical proof is in article.tex; these finite tests do not replace it.
"""
from __future__ import annotations

import argparse
import csv
import json
from dataclasses import dataclass
from fractions import Fraction as Q
from functools import lru_cache
from itertools import product
from math import comb
from pathlib import Path
from typing import Optional

Point = Optional[tuple[Q, Q]]  # None denotes the point at infinity.


@dataclass(frozen=True)
class Curve:
    a: int
    b: int
    c: int
    d: int

    @property
    def delta(self) -> int:
        return self.a * self.b * self.d - self.b**2 * self.c + self.d**2

    @property
    def kappa(self) -> int:
        return self.b**4

    @property
    def s(self) -> int:
        return self.a * self.b + 2 * self.d + 2

    @property
    def L(self) -> int:
        return self.delta + self.s - 1

    @property
    def discriminant(self) -> int:
        b2 = self.a**2 + 4 * self.c
        b4 = self.a * self.b + 2 * self.d
        b6 = self.b**2
        b8 = -self.delta
        return -b2**2 * b8 - 8*b4**3 - 27*b6**2 + 9*b2*b4*b6

    def on_curve(self, p: Point) -> bool:
        if p is None:
            return True
        x, y = p
        return y*y + self.a*x*y + self.b*y == x**3 + self.c*x*x + self.d*x

    def add(self, p: Point, q: Point) -> Point:
        """The ordinary generalized-Weierstrass group law, not the J-map."""
        if p is None:
            return q
        if q is None:
            return p
        x1, y1 = p
        x2, y2 = q
        if x1 == x2:
            if y1 + y2 + self.a*x1 + self.b == 0:
                return None
            if p != q:
                raise ArithmeticError("Inconsistent points with the same x-coordinate")
            slope = (3*x1*x1 + 2*self.c*x1 + self.d - self.a*y1) / (
                2*y1 + self.a*x1 + self.b
            )
        else:
            slope = (y2-y1)/(x2-x1)
        intercept = y1 - slope*x1
        x3 = slope*slope + self.a*slope - self.c - x1 - x2
        y3 = -(slope+self.a)*x3 - intercept - self.b
        result = (x3, y3)
        assert self.on_curve(result)
        return result

    def multiples(self, n: int) -> list[Point]:
        p: Point = (Q(0), Q(0))
        out: list[Point] = [None]
        for _ in range(n):
            out.append(self.add(out[-1], p))
        return out


def moments(curve: Curve, n: int) -> tuple[list[int], list[int]]:
    """Return q_0,...,q_n and mu_0,...,mu_n using division-free recurrences."""
    if n < 0:
        raise ValueError("n must be nonnegative")
    q = [1]
    for k in range(1, n+1):
        value = -curve.s*q[k-1]
        if k == 1:
            value += curve.s-1
        if k >= 2:
            value -= curve.L*q[k-2]
        if k >= 3:
            value += curve.kappa*sum(q[i]*q[k-3-i] for i in range(k-2))
        q.append(value)
    mu = [1]
    for k in range(1, n+1):
        mu.append(mu[k-1] + sum(q[i]*mu[k-2-i] for i in range(k-1)))
    return q, mu


def catalan_formula(curve: Curve, n: int) -> int:
    """Independent finite-sum evaluation of q_n (Appendix B)."""
    total = 0
    for k in range(n//3+1):
        cat = comb(2*k,k)//(k+1)
        for j in range(min(k+1,n-3*k)+1):
            m = n-3*k-j
            inner = sum((-1)**(m-ell)*comb(2*k+m-ell,m-ell)*comb(m-ell,ell)
                        *curve.s**(m-2*ell)*curve.L**ell for ell in range(m//2+1))
            total += cat*curve.kappa**k*comb(k+1,j)*(curve.s-1)**j*inner
    return total


def determinant(matrix: list[list[int]]) -> int:
    """Fraction-free Bareiss determinant, with row pivoting and exact divisions."""
    n = len(matrix)
    if any(len(row) != n for row in matrix):
        raise ValueError("A square matrix is required")
    if n == 0:
        return 1
    a = [row[:] for row in matrix]
    sign, previous = 1, 1
    for k in range(n-1):
        if a[k][k] == 0:
            pivot_row = next((i for i in range(k+1, n) if a[i][k]), None)
            if pivot_row is None:
                return 0
            a[k], a[pivot_row] = a[pivot_row], a[k]
            sign = -sign
        pivot = a[k][k]
        for i in range(k+1, n):
            for j in range(k+1, n):
                numerator = a[i][j]*pivot - a[i][k]*a[k][j]
                value, remainder = divmod(numerator, previous)
                assert remainder == 0, "Bareiss division was not exact"
                a[i][j] = value
            a[i][k] = 0
        previous = pivot
    return sign*a[-1][-1]


def hankels(mu: list[int], n: int) -> tuple[list[int], list[int]]:
    if len(mu) < 2*n+2:
        raise ValueError("Need moments through mu_(2n+1)")
    h, hs = [], []
    for k in range(n+1):
        h.append(determinant([[mu[i+j] for j in range(k+1)] for i in range(k+1)]))
        hs.append(determinant([
            [mu[i+j+(i == k)] for j in range(k+1)] for i in range(k+1)
        ]))
    return h, hs


def inverse_series(f: list[Q]) -> list[Q]:
    if not f or f[0] == 0:
        raise ValueError("Series must have nonzero constant term")
    out = [1/f[0]]
    for n in range(1, len(f)):
        out.append(-sum(f[k]*out[n-k] for k in range(1, n+1))/f[0])
    return out


def strip_j_fraction(mu: list[int], depth: int) -> tuple[list[Q], list[Q]]:
    """Extract coefficients directly from the moment series, independently of E."""
    f = [Q(x) for x in mu]
    alpha: list[Q] = []
    beta: list[Q] = [Q(0)]
    for _ in range(depth+1):
        if len(f) < 3:
            raise ValueError("Insufficient moments for requested depth")
        inv = inverse_series(f)
        alpha.append(-inv[1])
        beta.append(-inv[2])
        if beta[-1] == 0:
            break
        f = [-x/beta[-1] for x in inv[2:]]
        assert f[0] == 1
    return alpha, beta


def division_values(curve: Curve, n: int) -> list[Q]:
    """Classical doubling/odd division-polynomial recurrences evaluated at P.

    These only divide by psi_2(P)=b, not by possibly vanishing later terms.
    Consequently the same evaluator works at torsion points.
    """
    if not curve.b:
        raise ValueError("This evaluator requires b != 0")

    @lru_cache(None)
    def psi(k: int) -> Q:
        if k == 0:
            return Q(0)
        if k == 1:
            return Q(1)
        if k == 2:
            return Q(curve.b)
        if k == 3:
            return Q(-curve.delta)
        if k == 4:
            return Q(-curve.b*((curve.s-2)*curve.delta+curve.kappa))
        m = k//2
        if k % 2:
            return psi(m+2)*psi(m)**3 - psi(m-1)*psi(m+1)**3
        return psi(m)*(psi(m-1)**2*psi(m+2)-psi(m-2)*psi(m+1)**2)/curve.b

    return [psi(k) for k in range(n+1)]


def check_curve(curve: Curve, depth: int) -> dict:
    assert curve.b and curve.discriminant
    _, mu = moments(curve, 2*depth+3)
    h, hs = hankels(mu, depth+1)
    psis = division_values(curve, depth+2)
    for n in range(depth+2):
        assert Q(h[n]) == Q(curve.b)**(n*n-2*n)*psis[n+1]
    pts = curve.multiples(depth+2)
    alpha, beta = strip_j_fraction(mu, depth)
    assert alpha[:2] == [1, -1]
    assert beta[1] == 1
    checked = 0
    for m in range(2, depth+1):
        p = pts[m]
        if p is None or p[0] == 0:
            break
        x, y = p
        u, v = curve.b*y/x - curve.d - 1, -curve.b**2*x
        assert m < len(alpha), "Stripping stopped before a nondegenerate point"
        assert alpha[m] == u and beta[m] == v
        assert v*v+(u*u+curve.s*u+curve.L)*v-curve.kappa*(u+1) == 0
        assert Q(h[m]*h[m-2], h[m-1]**2) == v
        assert Q(hs[m], h[m])-Q(hs[m-1], h[m-1]) == u
        recovered_x = -Q(h[m-2]*h[m], curve.b**2*h[m-1]**2)
        recovered_y = recovered_x/curve.b*(u+curve.d+1)
        assert (recovered_x, recovered_y) == p
        next_p = pts[m+1]
        vp = -v-u*u-curve.s*u-curve.L
        assert vp == -Q(curve.kappa)*(u+1)/v
        if next_p is not None:
            assert vp == -curve.b**2*next_p[0]
            if vp:
                up = Q(curve.kappa)/vp-curve.s-u
                assert up == curve.b*next_p[1]/next_p[0]-curve.d-1
        checked += 1
    return {
        "parameters": [curve.a, curve.b, curve.c, curve.d],
        "discriminant": curve.discriminant,
        "nondegenerate_layers_checked": checked,
        "division_identity_last_hankel_index": depth+1,
    }


def finite_field_count(curve: Curve, p: int) -> int:
    return 1+sum((y*y+curve.a*x*y+curve.b*y-x**3-curve.c*x*x-curve.d*x) % p == 0
                 for x in range(p) for y in range(p))


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=Path("data"))
    parser.add_argument("--depth", type=int, default=8)
    args = parser.parse_args()
    if args.depth < 3:
        parser.error("--depth must be at least 3")
    out: Path = args.output
    out.mkdir(parents=True, exist_ok=True)

    # Exhaustive grid: not a random sample; singular curves are listed separately.
    grid = [Curve(a,b,c,d) for a,b,c,d in product(range(-1,2), (-2,-1,1,2),
                                                range(-1,2), range(-1,2))]
    singular = [c for c in grid if c.discriminant == 0]
    tested = [check_curve(c, args.depth) for c in grid if c.discriminant != 0]
    examples = {
        "barry": Curve(2,5,4,9),
        "infinite_order": Curve(0,1,0,-1),
        "order_three": Curve(0,1,0,0),
        "order_four": Curve(1,1,1,0),
    }
    example_data = {}
    for name, curve in examples.items():
        check_curve(curve, args.depth)
        q, mu = moments(curve, 40)
        for n in range(21):
            assert q[n] == catalan_formula(curve,n)
        h, hs = hankels(mu, 12)
        psi = division_values(curve, 13)
        pts = curve.multiples(12)
        for n in range(13):
            assert Q(h[n]) == Q(curve.b)**(n*n-2*n)*psi[n+1]
        with (out/f"{name}_moments.csv").open("w", newline="") as f:
            w = csv.writer(f); w.writerow(["n", "q_n", "mu_n"])
            w.writerows((n,q[n],mu[n]) for n in range(len(mu)))
        with (out/f"{name}_hankels.csv").open("w", newline="") as f:
            w = csv.writer(f); w.writerow(["n", "h_n", "h_n_star", "normalized_h_n"])
            w.writerows((n,h[n],hs[n],str(Q(h[n])*Q(curve.b)**(-n*n+2*n)))
                        for n in range(len(h)))
        with (out/f"{name}_points.csv").open("w", newline="") as f:
            w = csv.writer(f); w.writerow(["m", "X_m", "Y_m", "alpha_m", "beta_m"])
            for m,p in enumerate(pts):
                if p is None:
                    w.writerow([m, "infinity", "infinity", "undefined", "undefined"])
                else:
                    x,y = p
                    u = curve.b*y/x-curve.d-1 if x else "undefined"
                    w.writerow([m,str(x),str(y),str(u),str(-curve.b**2*x)])
        example_data[name] = {
            "parameters": [curve.a,curve.b,curve.c,curve.d],
            "discriminant": curve.discriminant,
            "moments_0_to_12": mu[:13],
            "hankels_0_to_8": h[:9],
            "normalized_hankels_0_to_8": [str(Q(h[n])*Q(curve.b)**(-n*n+2*n)) for n in range(9)],
            "finite_field_counts": {str(p):finite_field_count(curve,p) for p in (3,5,7)
                                    if curve.discriminant % p},
        }
    assert examples["order_three"].multiples(3)[3] is None
    assert examples["order_four"].multiples(4)[4] is None
    assert example_data["order_three"]["hankels_0_to_8"][2:4] == [0, -1]
    summary = {
        "arithmetic": "exact integers and fractions; no floating point",
        "grid": "a,c,d in {-1,0,1}; b in {-2,-1,1,2}",
        "grid_total": len(grid), "nonsingular_curves_tested":len(tested),
        "singular_curves_skipped":len(singular),
        "depth":args.depth,
        "nondegenerate_layers_checked":sum(t["nondegenerate_layers_checked"] for t in tested),
        "finite_sum_checks": 84,
        "status":"ALL CHECKS PASSED", "curves":tested, "examples":example_data,
    }
    (out/"verification.json").write_text(json.dumps(summary, indent=2)+"\n")
    print(json.dumps({k:v for k,v in summary.items() if k not in ("curves",)}, indent=2))


if __name__ == "__main__":
    main()
