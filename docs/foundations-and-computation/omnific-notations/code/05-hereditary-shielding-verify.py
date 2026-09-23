#!/usr/bin/env python3
"""Exact finite regression checks for Equality for Omnific Notations.

Python 3.9+, standard library only. These tests are NOT proofs of the
infinite theorems, algorithms for the halting set, or a Lean formalization.
Run from any directory; results go to ../data/verification.json.
"""
from __future__ import annotations

from collections import Counter
from dataclasses import dataclass
from datetime import datetime, timezone
from fractions import Fraction as Q
from functools import cmp_to_key
from itertools import permutations, product
from pathlib import Path
import json
import random
import sys

COUNTS = Counter()


def check(category, condition, detail=""):
    COUNTS[category] += 1
    if not condition:
        raise AssertionError(category + ": " + detail)


def sign(x):
    return (x > 0) - (x < 0)


# Hereditary finite normal forms. Constants are terms with exponent ZERO.
@dataclass(frozen=True)
class H:
    terms: tuple  # tuples (canonical H exponent, nonzero Fraction coefficient)


ZERO = H(())


def hcmp(x, y):
    i = j = 0
    while i < len(x.terms) or j < len(y.terms):
        if i == len(x.terms):
            return -sign(y.terms[j][1])
        if j == len(y.terms):
            return sign(x.terms[i][1])
        ex, ax = x.terms[i]
        ey, ay = y.terms[j]
        c = hcmp(ex, ey)
        if c:
            return sign(ax) if c > 0 else -sign(ay)
        if ax != ay:
            return sign(ax - ay)
        i += 1
        j += 1
    return 0


def hnorm(terms):
    d = {}
    for exponent, coefficient in terms:
        d[exponent] = d.get(exponent, Q(0)) + Q(coefficient)
    exponents = sorted((e for e in d if d[e]), key=cmp_to_key(hcmp), reverse=True)
    return H(tuple((e, d[e]) for e in exponents))


def const(q):
    q = Q(q)
    return H(((ZERO, q),)) if q else ZERO


ONE = const(1)


def hadd(x, y):
    return hnorm(x.terms + y.terms)


def hneg(x):
    return H(tuple((e, -a) for e, a in x.terms))


def hsub(x, y):
    return hadd(x, hneg(y))


def hmul(x, y):
    return hnorm((hadd(e, f), a * b) for e, a in x.terms for f, b in y.terms)


def omega(exponent):
    return H(((exponent, Q(1)),))


def omnific(x):
    return all(hcmp(e, ZERO) >= 0 and (e != ZERO or a.denominator == 1)
               for e, a in x.terms)


def hfloor(x):
    positive = hnorm((e, a) for e, a in x.terms if hcmp(e, ZERO) > 0)
    negative = hnorm((e, a) for e, a in x.terms if hcmp(e, ZERO) < 0)
    c = dict(x.terms).get(ZERO, Q(0))
    m = c.numerator // c.denominator
    if c == m and hcmp(negative, ZERO) < 0:
        m -= 1
    return hadd(positive, const(m))


def hereditary_checks():
    rng = random.Random(20260923)
    exps = [const(q) for q in (-3, -1, Q(-1, 2), 0, Q(1, 2), 1, 2)]
    w = omega(ONE)
    exps += [w, hneg(w), hadd(w, ONE), hsub(w, ONE)]

    def sample():
        return hnorm((rng.choice(exps), Q(rng.randint(-3, 3), rng.randint(1, 3)))
                     for _ in range(rng.randrange(1, 5)))

    for _ in range(100):
        a, b, c = sample(), sample(), sample()
        check("hereditary identities", hadd(a, b) == hadd(b, a), "addition")
        check("hereditary identities", hmul(a, b) == hmul(b, a), "multiplication")
        check("hereditary identities", hadd(hadd(a, b), c) == hadd(a, hadd(b, c)), "associativity")
        check("hereditary identities", hmul(a, hadd(b, c)) == hadd(hmul(a, b), hmul(a, c)), "distributivity")
        check("hereditary identities", hsub(a, a) == ZERO, "cancellation")
        check("hereditary order", hcmp(a, b) == hcmp(hadd(a, c), hadd(b, c)), "translation")
        check("hereditary order", hcmp(a, b) == -hcmp(b, a), "antisymmetry")
        check("hereditary order", (hcmp(a, b) == 0) == (a == b), "canonical equality")
        check("hereditary order", hcmp(hmul(a, a), ZERO) >= 0, "square")
        floor = hfloor(a)
        check("omnific floor", omnific(floor), "membership")
        check("omnific floor", hcmp(floor, a) <= 0, "lower bound")
        check("omnific floor", hcmp(a, hadd(floor, ONE)) < 0, "upper bound")
        check("omega identities", hmul(omega(a), omega(b)) == omega(hadd(a, b)))

    check("omnific floor", hfloor(hsub(w, omega(const(-1)))) == hsub(w, ONE))
    check("omnific floor", hfloor(hsub(hadd(w, const(Q(1, 2))), omega(const(-1)))) == w)
    check("hereditary identities", hmul(hadd(w, ONE), hadd(w, ONE)) ==
          hnorm([(const(2), 1), (ONE, 2), (ZERO, 1)]))


# Sparse multivariate polynomials, represented by multi-index -> Fraction.
def pconst(c, r):
    c = Q(c)
    return {(0,) * r: c} if c else {}


def padd(a, b):
    out = dict(a)
    for n, c in b.items():
        out[n] = out.get(n, Q(0)) + c
        if not out[n]:
            del out[n]
    return out


def pscale(a, c):
    return {n: v * c for n, v in a.items() if v * c}


def pmul(a, b):
    out = {}
    for n, c in a.items():
        for m, d in b.items():
            k = tuple(x + y for x, y in zip(n, m))
            out[k] = out.get(k, Q(0)) + c * d
            if not out[k]:
                del out[k]
    return out


def pdet(a, r):
    d = len(a)
    out = {}
    for perm in permutations(range(d)):
        inv = sum(perm[i] > perm[j] for i in range(d) for j in range(i + 1, d))
        term = pconst((-1) ** inv, r)
        for i in range(d):
            term = pmul(term, a[i][perm[i]])
        out = padd(out, term)
    return out


def padj(a, r):
    d = len(a)
    return [[pscale(pdet([[a[k][l] for l in range(d) if l != i]
                         for k in range(d) if k != j], r), (-1) ** (i + j))
             for j in range(d)] for i in range(d)]


def pmatmul(a, b):
    return [[sum_poly(pmul(a[i][k], b[k][j]) for k in range(len(b)))
             for j in range(len(b[0]))] for i in range(len(a))]


def sum_poly(terms):
    out = {}
    for term in terms:
        out = padd(out, term)
    return out


def matmul(a, b):
    return [[sum(a[i][k] * b[k][j] for k in range(len(b)))
             for j in range(len(b[0]))] for i in range(len(a))]


def identity(d):
    return [[Q(i == j) for j in range(d)] for i in range(d)]


def matpow(a, n):
    out = identity(len(a))
    for _ in range(n):
        out = matmul(out, a)
    return out


def coefficient(u, matrices, v, n):
    state = [[Q(x)] for x in v]
    for m, exponent in zip(reversed(matrices), reversed(n)):
        state = matmul(matpow(m, exponent), state)
    return sum(Q(x) * state[i][0] for i, x in enumerate(u))


def rational_numerator(u, matrices, v):
    d, r = len(v), len(matrices)
    left = [[pconst(x, r) for x in u]]
    denominator = pconst(1, r)
    for index, m in enumerate(matrices):
        ei = tuple(int(j == index) for j in range(r))
        a = [[padd(pconst(i == j, r), {ei: -Q(m[i][j])} if m[i][j] else {})
              for j in range(d)] for i in range(d)]
        denominator = pmul(denominator, pdet(a, r))
        left = pmatmul(left, padj(a, r))
    numerator = pmatmul(left, [[pconst(x, r)] for x in v])[0][0]
    return numerator, denominator


def weight(n, deltas):
    return tuple(sum(Q(ni) * di[k] for ni, di in zip(n, deltas))
                 for k in range(len(deltas[0])))


def pevaluate_weights(p, deltas):
    out = {}
    for n, c in p.items():
        w = weight(n, deltas)
        out[w] = out.get(w, Q(0)) + c
        if not out[w]:
            del out[w]
    return out


def matrix_checks():
    rng = random.Random(39153)
    for d in (1, 2, 3):
        for r in (1, 2):
            for _ in range(8):
                base = [[Q(rng.randint(-2, 2)) for _ in range(d)] for _ in range(d)]
                # Polynomials of a shared matrix commute. Includes nilpotent,
                # diagonal, zero-output, and cancellation instances by chance.
                matrices = []
                for _ in range(r):
                    a, b = rng.randint(-2, 2), rng.randint(-2, 2)
                    matrices.append([[a * base[i][j] + Q(b * (i == j))
                                      for j in range(d)] for i in range(d)])
                u = [Q(rng.randint(-2, 2)) for _ in range(d)]
                v = [Q(rng.randint(-2, 2)) for _ in range(d)]
                p, q = rational_numerator(u, matrices, v)
                check("matrix numerator bounds", all(all(ni <= d - 1 for ni in n) for n in p))
                check("matrix numerator bounds", q.get((0,) * r) == 1)
                for n in product(range(d + 2), repeat=r):
                    lhs = sum(c * coefficient(u, matrices, v, tuple(ni - mi for ni, mi in zip(n, m)))
                              for m, c in q.items() if all(mi <= ni for ni, mi in zip(n, m)))
                    check("matrix QF=P coefficients", lhs == p.get(n, 0), str((d, r, n)))
                deltas = [tuple(Q(i == j) for j in range(r)) for i in range(r)]
                pw = pevaluate_weights(p, deltas)
                front = {weight(n, deltas): coefficient(u, matrices, v, n)
                         for n in product(range(d), repeat=r) if sum(n) < d}
                front = {w: c for w, c in front.items() if c}
                check("independent finite front", bool(pw) == bool(front))
                if pw:
                    lp, lf = min(pw), min(front)
                    check("independent finite front", lp == lf and pw[lp] == front[lf])

    n = [[Q(0), Q(0)], [Q(1), Q(0)]]
    m2 = [[Q(1), Q(0)], [Q(-1), Q(1)]]
    u, v = [0, 1], [1, 0]
    p, q = rational_numerator(u, [n, m2], v)
    check("collision regression", p == {(1, 0): Q(1), (0, 1): Q(-1), (1, 1): Q(-1)})
    check("collision regression", q == {(0, 0): Q(1), (0, 1): Q(-2), (0, 2): Q(1)})
    collapsed = pevaluate_weights(p, [(Q(1),), (Q(1),)])
    check("collision regression", collapsed == {(Q(2),): Q(-1)})
    for k in range(12):
        c = sum(coefficient(u, [n, m2], v, (i, k - i)) for i in range(k + 1))
        expected = Q(0) if k < 2 else Q(-(k - 1))
        check("collision regression", c == expected, str(k))

    # Nilpotent examples attain total-degree bound d-1 in one variable.
    for d in range(1, 9):
        shift = [[Q(i == j + 1) for j in range(d)] for i in range(d)]
        u = [Q(i == d - 1) for i in range(d)]
        v = [Q(i == 0) for i in range(d)]
        for k in range(d + 2):
            check("sharp state-dimension bound", coefficient(u, [shift], v, (k,)) == Q(k == d - 1))


# Explicit order-embedding of finite sequences in dyadic rationals.
def dyadic_code(sequence):
    l, r = Q(0), Q(1)
    for n in sequence:
        if n < 0:
            raise ValueError("Tree digits must be nonnegative")
        length = r - l
        l, r = l + length * (1 - Q(1, 2 ** n)), l + length * (1 - Q(1, 2 ** (n + 1)))
    return r


def dyadic_inverse(q):
    q = Q(q)
    if q == 1:
        return ()
    if not 0 < q < 1 or q.denominator & (q.denominator - 1):
        raise ValueError("Expected a dyadic in (0,1]")
    length = q.denominator.bit_length() - 1
    bits = format(q.numerator - 1, "0%db" % length)
    out, count = [], 0
    for bit in bits:
        if bit == "1":
            count += 1
        else:
            out.append(count)
            count = 0
    if count:
        raise AssertionError("A reduced dyadic code must end in zero")
    return tuple(out)


def kb_compare(s, t):
    for a, b in zip(s, t):
        if a != b:
            return sign(a - b)
    # Extensions precede proper prefixes.
    return sign(len(t) - len(s))


def dyadic_checks():
    sequences = [s for length in range(5) for s in product(range(3), repeat=length)]
    for s in sequences:
        q = dyadic_code(s)
        check("dyadic inverse", dyadic_inverse(q) == s)
        check("dyadic interval", 1 <= 2 - q < 2)
    for s in sequences:
        for t in sequences:
            check("Kleene-Brouwer order", kb_compare(s, t) == sign(dyadic_code(s) - dyadic_code(t)))
    for length in range(1, 10):
        for m in range(1, 2 ** length, 2):
            q = Q(m, 2 ** length)
            check("dyadic surjectivity", dyadic_code(dyadic_inverse(q)) == q)


# Exact finite Hankel ranks for known switch fixtures (not halting oracles).
def rational_rank(matrix):
    a = [[Q(x) for x in row] for row in matrix]
    rows, cols = len(a), len(a[0]) if a else 0
    pivot = 0
    for col in range(cols):
        k = next((i for i in range(pivot, rows) if a[i][col]), None)
        if k is None:
            continue
        a[pivot], a[k] = a[k], a[pivot]
        c = a[pivot][col]
        a[pivot] = [x / c for x in a[pivot]]
        for i in range(rows):
            if i != pivot and a[i][col]:
                c = a[i][col]
                a[i] = [x - c * y for x, y in zip(a[i], a[pivot])]
        pivot += 1
        if pivot == rows:
            break
    return pivot


def realization_checks():
    for s in range(13):
        size = s + 3
        sequence = lambda n: Q(1 + int(n >= s))
        hankel = [[sequence(i + j) for j in range(size)] for i in range(size)]
        check("switch Hankel rank", rational_rank(hankel) == s + 1, str(s))
        for n in range(30):
            # Coefficients of (1+t^s)/(1-t), including the s=0 case.
            lhs = sequence(n) - (sequence(n - 1) if n else Q(0))
            rhs = Q(int(n == 0) + int(n == s))
            check("switch rational identity", lhs == rhs)
        # A concrete shift-window realization of dimension s+1.
        d = s + 1
        transition = [[Q(j == i + 1) for j in range(d)] for i in range(d)]
        transition[-1] = [Q(j == d - 1) for j in range(d)]
        initial = [sequence(i) for i in range(d)]
        output = [Q(i == 0) for i in range(d)]
        for n in range(20):
            check("switch matrix realization", coefficient(output, [transition], initial, (n,)) == sequence(n))
    check("switch Hankel rank", rational_rank([[1] * 16 for _ in range(16)]) == 1)


def main():
    hereditary_checks()
    matrix_checks()
    dyadic_checks()
    realization_checks()
    result = {
        "status": "PASS",
        "utc_timestamp": datetime.now(timezone.utc).isoformat(),
        "python_version": sys.version,
        "arithmetic": "fractions.Fraction; no floating-point arithmetic",
        "random_seeds": [20260923, 39153],
        "checks_by_category": dict(sorted(COUNTS.items())),
        "total_assertions": sum(COUNTS.values()),
        "scope": "Finite regressions only; not formal proofs or computations of undecidable predicates."
    }
    output = Path(__file__).resolve().parents[1] / "data" / "verification.json"
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
