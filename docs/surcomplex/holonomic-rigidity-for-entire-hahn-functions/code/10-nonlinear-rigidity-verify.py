#!/usr/bin/env python3
"""Exact finite checks for the accompanying Hahn rigidity manuscript.

Python 3.9+; standard library only.  These tests check finite identities,
not infinite Hahn summability, theorems, historical priority, or Lean proofs.
The output path must be explicit so the shipped record is not overwritten
accidentally. No assertions are used: checks remain active under python -O.
"""
from __future__ import annotations

import argparse
from collections import Counter
from fractions import Fraction as Q
import json
from pathlib import Path
import platform
import random
import sys
from typing import Dict, Iterable, List, Tuple

Exp = Tuple[int, ...]
Poly = Dict[Exp, Q]
Term = Tuple[int, Tuple[int, ...], Q]


class Checks:
    def __init__(self) -> None:
        self.counts: Counter = Counter()

    def check(self, condition: bool, group: str, message: str) -> None:
        if not condition:
            raise ArithmeticError(f"{group}: {message}")
        self.counts[group] += 1


def clean(p: Poly) -> Poly:
    return {e: Q(c) for e, c in p.items() if c}


def add(p: Poly, q: Poly) -> Poly:
    out = dict(p)
    for e, c in q.items():
        out[e] = out.get(e, Q(0)) + c
    return clean(out)


def scale(p: Poly, c: Q) -> Poly:
    return clean({e: c * a for e, a in p.items()})


def mul(p: Poly, q: Poly) -> Poly:
    out: Poly = {}
    for e, a in p.items():
        for f, b in q.items():
            ef = tuple(x + y for x, y in zip(e, f))
            out[ef] = out.get(ef, Q(0)) + a * b
    return clean(out)


def power(p: Poly, n: int, dim: int) -> Poly:
    if n < 0:
        raise ValueError("Polynomial powers must be nonnegative")
    out: Poly = {(0,) * dim: Q(1)}
    while n:
        if n & 1:
            out = mul(out, p)
        n //= 2
        if n:
            p = mul(p, p)
    return out


def falling(n: int, j: int) -> int:
    ans = 1
    for a in range(j):
        ans *= n - a
    return ans


def derivative(p: Poly, order: int = 1, variable: int = 0) -> Poly:
    out: Poly = {}
    for e, c in p.items():
        if e[variable] >= order:
            f = list(e)
            f[variable] -= order
            out[tuple(f)] = c * falling(e[variable], order)
    return clean(out)


def shift(p: Poly, e: Exp) -> Poly:
    return {tuple(a + b for a, b in zip(f, e)): c for f, c in p.items()}


def degree(p: Poly) -> int:
    return max((e[0] for e in p), default=-1)


def evaluate(p: Poly, n: int) -> Q:
    return sum((a * Q(n) ** e[0] for e, a in p.items()), Q(0))


def fall_poly(j: int) -> Poly:
    p: Poly = {(0,): Q(1)}
    for a in range(j):
        p = mul(p, {(1,): Q(1), (0,): Q(-a)})
    return clean(p)


def combined(terms: Iterable[Term]) -> List[Term]:
    data: Dict[Tuple[int, Tuple[int, ...]], Q] = {}
    for k, ms, c in terms:
        key = (k, ms)
        data[key] = data.get(key, Q(0)) + c
    return [(k, ms, c) for (k, ms), c in sorted(data.items()) if c]


def dw(k: int, ms: Tuple[int, ...]) -> Tuple[int, int]:
    return sum(ms), k - sum(j * m for j, m in enumerate(ms))


def corner(terms: List[Term]) -> Tuple[int, int, Poly, Q]:
    if not terms:
        raise ValueError("The zero equation has no selected corner")
    D = max(sum(ms) for _, ms, _ in terms)
    W = max(dw(k, ms)[1] for k, ms, _ in terms if sum(ms) == D)
    I: Poly = {}
    B = Q(0)
    for k, ms, c in terms:
        d, w = dw(k, ms)
        if d < D:
            B = max(B, Q(w - W, D - d))
        if (d, w) == (D, W):
            p: Poly = {(0,): c}
            for j, m in enumerate(ms):
                p = mul(p, power(fall_poly(j), m, 1))
            I = add(I, p)
    return D, W, I, B


def apply_terms(terms: List[Term], f: Poly) -> Poly:
    order = max(len(ms) for _, ms, _ in terms) - 1
    jets = [derivative(f, j) for j in range(order + 1)]
    out: Poly = {}
    for k, ms, c in terms:
        p: Poly = {(k,): c}
        for j, m in enumerate(ms):
            p = mul(p, power(jets[j], m, 1))
        out = add(out, p)
    return out


def nonzero(rng: random.Random) -> Q:
    return Q(rng.choice((-3, -2, -1, 1, 2, 3)))


def test_univariate(rng: random.Random, checks: Checks) -> None:
    for _ in range(240):
        s = rng.randint(0, 3)
        D = rng.randint(1, 3)
        W = rng.randint(0, 3)
        terms: List[Term] = []
        for _ in range(8):
            ms = [0] * (s + 1)
            for _ in range(D):
                ms[rng.randint(0, s)] += 1
            k = W + sum(j * m for j, m in enumerate(ms))
            terms.append((k, tuple(ms), nonzero(rng)))
        terms = combined(terms)
        if not terms:
            terms = [(W, (D,) + (0,) * s, Q(1))]
        N = rng.randint(max(1, s), 8)
        f = clean({(n,): Q(rng.randint(-2, 2)) for n in range(N)})
        f[(N,)] = nonzero(rng)
        d, w, I, _ = corner(terms)
        val = apply_terms(terms, f)
        target = d * N + w
        predicted = f[(N,)] ** d * evaluate(I, N)
        checks.check(degree(val) <= target, "higher_order_corner", "degree bound")
        checks.check(val.get((target,), Q(0)) == predicted,
                     "higher_order_corner", "falling-factorial top coefficient")

    for _ in range(240):
        terms = combined((rng.randint(0, 5),
                          (rng.randint(0, 3), rng.randint(0, 3)), nonzero(rng))
                         for _ in range(10))
        _, _, I, _ = corner(terms)
        checks.check(bool(I), "first_order_nondegeneracy", "corner vanished")


def weight(e: Exp, weights: Exp) -> int:
    return sum(a * b for a, b in zip(e, weights))


def euler(p: Poly, weights: Exp) -> Poly:
    return clean({e: c * weight(e, weights) for e, c in p.items()})


def homogeneous(p: Poly, N: int, weights: Exp) -> Poly:
    return {e: c for e, c in p.items() if weight(e, weights) == N}


def test_weighted(rng: random.Random, checks: Checks) -> None:
    weights = (1, 2)
    for _ in range(180):
        N, D, W = rng.randint(5, 9), rng.randint(1, 3), rng.randint(0, 5)
        f = clean({(a, b): Q(rng.randint(-2, 2))
                   for a in range(N + 1) for b in range(N // 2 + 1)
                   if a + 2 * b <= N and rng.randrange(4) == 0})
        f[(N, 0)] = nonzero(rng)
        Ef = euler(f, weights)
        pN = homogeneous(f, N, weights)
        HN: Poly = {}
        value: Poly = {}
        for b in range(W // 2 + 1):
            alpha = (W - 2 * b, b)
            for j in range(D + 1):
                c = nonzero(rng)
                HN = add(HN, {alpha: c * Q(N) ** j})
                term = mul(power(f, D - j, 2), power(Ef, j, 2))
                value = add(value, shift(scale(term, c), alpha))
        expected = mul(power(pN, D, 2), HN)
        actual = homogeneous(value, D * N + W, weights)
        checks.check(actual == expected, "weighted_euler", "top homogeneous identity")
        checks.check(all(weight(e, weights) <= D * N + W for e in value),
                     "weighted_euler", "weight bound")


def int_root_bound(p: Poly) -> int:
    """Strict integer bound larger than the absolute values of all complex roots."""
    n = degree(p)
    if n <= 0:
        return 1
    lead = abs(p[(n,)])
    bound = Q(1) + max((abs(c) / lead for e, c in p.items() if e[0] < n),
                      default=Q(0))
    return int(bound) + 1


def test_finite_hahn(rng: random.Random, checks: Checks) -> None:
    # Two polynomial coordinates: (z degree, integer t exponent). Negative t
    # exponents are legal. All objects here have finite supports.
    for _ in range(90):
        keys = {(rng.randint(0, 4), rng.randint(0, 2), rng.randint(0, 2))
                for _ in range(8)}
        keys.add((0, 2, 0))
        terms = []
        for k, i, j in sorted(keys):
            v = rng.randint(-3, 3)
            coeff = {(0, v): nonzero(rng),
                     (0, v + rng.randint(1, 3)): nonzero(rng)}
            terms.append((k, i, j, coeff))
        D = max(i + j for _, i, j, _ in terms)
        W = max(k - j for k, i, j, _ in terms if i + j == D)
        C = [(k, i, j, c) for k, i, j, c in terms
             if (i + j, k - j) == (D, W)]
        val = lambda c: min(e[1] for e in c)
        beta = min(val(c) for _, _, _, c in C)
        H: Poly = {}
        for _, _, j, c in C:
            H = add(H, {(j,): c.get((0, beta), Q(0))})
        checks.check(bool(H), "finite_hahn_certificate", "residue corner nonzero")
        B = max([Q(0)] + [Q(k - j - W, D - i - j)
                          for k, i, j, _ in terms if i + j < D])
        M = int_root_bound(H)
        m = max(M + 1, int(B) + 2)
        f: Poly = {}
        av = {}
        for n in range(m + 1):
            if n < m and rng.randrange(3) == 0:
                continue
            v = rng.randint(-3, 5)
            av[n] = v
            f[(n, v)] = nonzero(rng)
            f[(n, v + 1)] = nonzero(rng)
        rhs: List[int] = [av[m] - av[n] for n in av if n <= M]
        inequalities = [(m - n, av[m] - av[n]) for n in av if n <= M]
        for k, i, j, c in terms:
            d, w = i + j, k - j
            if d == D and w < W:
                inequalities.append((W - w, beta - val(c)))
            if d < D:
                inequalities.append(((D - d) * m + W - w,
                                     beta - val(c) + (D - d) * av[m]))
        rhs = [b for _, b in inequalities]
        r = 1 + max([0] + [abs(b) for b in rhs])
        checks.check(all(a > 0 and a * r > b for a, b in inequalities),
                     "finite_hahn_certificate", "certificate inequalities")
        scaled = {(n, e - n * r): c for (n, e), c in f.items()}
        h = min(e for _, e in scaled)
        p = {(n,): c for (n, e), c in scaled.items() if e == h}
        N = degree(p)
        checks.check(N > M and h <= av[m] - m * r,
                     "finite_hahn_certificate", "active index and h bound")
        fp = derivative(f)
        pf: Poly = {}
        for k, i, j, c in terms:
            term = mul(c, mul(power(f, i, 2), power(fp, j, 2)))
            pf = add(pf, shift(term, (k, 0)))
        scaled_pf = {(n, e - n * r): c for (n, e), c in pf.items()}
        lam = beta + D * h - W * r
        initial = {(n,): c for (n, e), c in scaled_pf.items() if e == lam}
        checks.check(bool(scaled_pf) and min(e for _, e in scaled_pf) == lam,
                     "finite_hahn_certificate", "predicted Hahn leading layer")
        checks.check(initial.get((D * N + W,), Q(0)) == p[(N,)] ** D * evaluate(H, N)
                     and evaluate(H, N) != 0,
                     "finite_hahn_certificate", "nonzero corner coefficient")


def test_ordered_groups(rng: random.Random, checks: Checks) -> None:
    for _ in range(500):
        # Ordinary lexicographic order; the first coordinate has highest rank.
        dim = rng.randint(2, 5)
        zero = (0,) * dim
        eps = (0,) * (dim - 1) + (1,)
        rhs = [tuple(rng.randint(-15, 15) for _ in range(dim)) for _ in range(7)]
        absolutes = [max(v, tuple(-a for a in v)) for v in rhs]
        bound = max([zero] + absolutes)
        r = tuple(a + b for a, b in zip(bound, eps))
        multipliers = [rng.randint(1, 8) for _ in rhs]
        checks.check(r > zero and all(tuple(n * a for a in r) > v
                                     for n, v in zip(multipliers, rhs)),
                     "ordered_group_radius", "division-free higher-rank radius")


def test_examples(checks: Checks) -> dict:
    z: Poly = {(1,): Q(1)}
    riccati = [(0, (0, 1), Q(1)), (0, (2, 0), Q(-1)),
               (0, (0, 0), Q(-1)), (2, (0, 0), Q(1))]
    checks.check(apply_terms(riccati, z) == {}, "worked_examples", "Riccati f=z")
    D, W, I, B = corner(riccati)
    checks.check((D, W, I, B) == (2, 0, {(0,): Q(-1)}, Q(1)),
                 "worked_examples", "Riccati candidate bound")
    p1 = [(0, (0, 0, 1), Q(1)), (0, (2, 0, 0), Q(-6)),
          (1, (0, 0, 0), Q(-1))]
    p2 = [(0, (0, 0, 1), Q(1)), (0, (3, 0, 0), Q(-2)),
          (1, (1, 0, 0), Q(-1)), (0, (0, 0, 0), Q(-1))]
    checks.check(corner(p1)[2:] == ({(0,): Q(-6)}, Q(1, 2)),
                 "worked_examples", "Painleve I corner")
    checks.check(corner(p2)[2:] == ({(0,): Q(-2)}, Q(1, 2)),
                 "worked_examples", "Painleve II corner")
    degenerate = [(2, (1, 0, 1), Q(1)), (1, (1, 1, 0), Q(1)),
                  (2, (0, 2, 0), Q(-1))]
    checks.check(corner(degenerate)[2] == {}, "worked_examples", "zero second-order corner")
    for n in range(21):
        checks.check(apply_terms(degenerate, {(n,): Q(3, 2)}) == {},
                     "worked_examples", "monomial solution of degenerate equation")
    checks.check(bool(apply_terms(degenerate, {(0,): Q(1), (1,): Q(1)})),
                 "worked_examples", "nonmonomial fails degenerate equation")
    for m in range(1, 9):
        sharp = [(0, (0, 1), Q(1)), (0, (2, 0), Q(-1)),
                 (m - 1, (0, 0), Q(-m)), (2 * m, (0, 0), Q(1))]
        checks.check(apply_terms(sharp, {(m,): Q(1)}) == {} and corner(sharp)[3] == m,
                     "worked_examples", "slope cutoff attained")
        resonance = [(1, (1, 1), Q(1)), (0, (2, 0), Q(-m))]
        checks.check(apply_terms(resonance, {(m,): Q(2)}) == {}
                     and corner(resonance)[2] == {(1,): Q(1), (0,): Q(-m)},
                     "worked_examples", "integer resonance attained")
    c = Q(2, 3)
    for n in range(20):
        conv = sum((c ** (j + 1) * c ** (n - j + 1) for j in range(n + 1)), Q(0))
        checks.check(conv == (n + 1) * c ** (n + 2),
                     "worked_examples", "formal geometric Riccati identity")
    for N in range(20):
        monomials = [(N - 2 * j, j) for j in range(N // 2 + 1)]
        checks.check(len(monomials) == N // 2 + 1
                     and all(a + 2 * b == N for a, b in monomials),
                     "worked_examples", "weighted solution-space dimension")
    return {
        "riccati_f_equals_z": {"D": D, "W": W, "I(T)": "-1", "B": str(B)},
        "painleve_I": {"H(T)": "-6", "B": "1/2"},
        "painleve_II": {"H(T)": "-2", "B": "1/2"},
        "degenerate_corner": "T*(T-1)+T-T^2 = 0",
        "tested_degenerate_monomial_degrees": list(range(21)),
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--seed", type=int, default=20260922)
    args = parser.parse_args()
    if args.output.exists():
        parser.error("Output exists; use a new path to preserve prior records.")
    rng = random.Random(args.seed)
    checks = Checks()
    try:
        test_univariate(rng, checks)
        test_weighted(rng, checks)
        test_finite_hahn(rng, checks)
        test_ordered_groups(rng, checks)
        examples = test_examples(checks)
    except Exception as error:
        print(f"FAIL: {error}", file=sys.stderr)
        return 1
    record = {
        "status": "PASS",
        "seed": args.seed,
        "python": platform.python_version(),
        "arithmetic": "exact integer and fractions.Fraction; standard library only",
        "checks": sum(checks.counts.values()),
        "checks_by_group": dict(sorted(checks.counts.items())),
        "examples": examples,
        "scope": [
            "Finite polynomial identities and finite Hahn support calculations only.",
            "No numerical approximation of infinite surreal sums.",
            "No proof-assistant verification or independent refereeing.",
            "Infinite support arguments and all-rank theorems are proved in article.tex, not by testing."
        ],
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(record, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({"status": record["status"], "checks": record["checks"],
                      "checks_by_group": record["checks_by_group"]}, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
