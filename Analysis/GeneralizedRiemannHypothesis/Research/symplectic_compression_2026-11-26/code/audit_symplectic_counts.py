"""Independent small-field audit of the exact symplectic compression law.

This intentionally uses direct frame enumeration, not group enumeration, and
an integer product for frame counts rather than the likelihood expansion.
Only q=2,3,4 are implemented; F_4 is F_2[x]/(x^2+x+1).
"""

from collections import Counter
from fractions import Fraction
from functools import lru_cache
from itertools import product
import json
from pathlib import Path


class Field:
    def __init__(self, q):
        assert q in (2, 3, 4)
        self.q = q

    def add(self, a, b):
        return a ^ b if self.q == 4 else (a + b) % self.q

    def neg(self, a):
        return a if self.q == 4 else (-a) % self.q

    def mul(self, a, b):
        if self.q != 4:
            return (a * b) % self.q
        ans = 0
        while b:
            if b & 1:
                ans ^= a
            b >>= 1
            a <<= 1
            if a & 4:
                a ^= 7
        return ans

    def inverse(self, a):
        assert a
        for b in range(1, self.q):
            if self.mul(a, b) == 1:
                return b
        raise AssertionError("not a field")

    def rank(self, rows, width=None):
        if not rows:
            return 0
        a = [list(r) for r in rows]
        nr, nc = len(a), len(a[0])
        lead = 0
        for j in range(nc):
            pivot = next((i for i in range(lead, nr) if a[i][j]), None)
            if pivot is None:
                continue
            a[lead], a[pivot] = a[pivot], a[lead]
            inv = self.inverse(a[lead][j])
            a[lead] = [self.mul(inv, x) for x in a[lead]]
            for i in range(nr):
                if i == lead or not a[i][j]:
                    continue
                coeff = self.neg(a[i][j])
                a[i] = [self.add(x, self.mul(coeff, y))
                        for x, y in zip(a[i], a[lead])]
            lead += 1
            if lead == nr:
                break
        return lead

    def form(self, u, v):
        ans = 0
        for i in range(0, len(u), 2):
            ans = self.add(ans, self.mul(u[i], v[i + 1]))
            ans = self.add(ans, self.neg(self.mul(u[i + 1], v[i])))
        return ans

    def gram(self, columns):
        return tuple(tuple(self.form(u, v) for v in columns) for u in columns)


@lru_cache(None)
def gaussian(q, m, k):
    if k < 0 or k > m or m < 0:
        return 0
    if k in (0, m):
        return 1
    return gaussian(q, m - 1, k) + q ** (m - k) * gaussian(q, m - 1, k - 1)


def gl_order(q, k):
    out = 1
    for i in range(k):
        out *= q ** k - q ** i
    return out


def embeddings(q, n, d, s):
    if not (0 <= 2 * s <= d and d - s <= n):
        return 0
    out = 1
    for i in range(s):
        out *= (q ** (2 * (n - i)) - 1) * q ** (2 * (n - i) - 1)
    for i in range(d - 2 * s):
        out *= q ** (2 * (n - s) - i) - q ** i
    return out


def transverse_count(q, r, t0, t1, ell):
    c = r - t0 - t1
    assert c >= 0
    return sum(gaussian(q, t0, k) * gaussian(q, t1, k) * gl_order(q, k)
               * gaussian(q, c, ell - k)
               * q ** ((ell - k) * (t0 + t1 - k))
               for k in range(min(ell, t0, t1) + 1))


def expected_count(f, n, h1, h0, m):
    a, b = len(h1), len(h0)
    g = [list(h1[i]) + list(m[i]) for i in range(a)]
    g += [[f.neg(m[i][j]) for i in range(a)] + list(h0[j]) for j in range(b)]
    two_s = f.rank(g)
    assert two_s % 2 == 0
    s = two_s // 2
    r = a + b - two_s
    t0 = b - f.rank(list(h0) + list(m))
    t1 = a - f.rank(list(h1) + [tuple(m[i][j] for i in range(a)) for j in range(b)])
    numerator = sum(transverse_count(f.q, r, t0, t1, ell)
                    * embeddings(f.q, n, a + b - ell, s)
                    for ell in range(r + 1))
    denom = embeddings(f.q, n, a, f.rank(h1) // 2)
    result = Fraction(numerator, denom)
    assert (result > 0) == (s + max(t0, t1) <= n)
    assert result.denominator == 1
    return result.numerator


def basis_vector(dim, i):
    return tuple(int(j == i) for j in range(dim))


def verify_case(q, n, target_indices, source_indices):
    f = Field(q)
    dim = 2 * n
    y = tuple(basis_vector(dim, i) for i in target_indices)
    x0 = tuple(basis_vector(dim, i) for i in source_indices)
    a, b = len(y), len(x0)
    h1, h0 = f.gram(y), f.gram(x0)
    vectors = list(product(range(q), repeat=dim))
    observed = Counter()
    count = 0
    for x in product(vectors, repeat=b):
        if f.rank(x) != b or f.gram(x) != h0:
            continue
        m = tuple(tuple(f.form(u, v) for v in x) for u in y)
        observed[m] += 1
        count += 1
    expected_total = embeddings(q, n, b, f.rank(h0) // 2)
    assert count == expected_total
    sum_expected = 0
    for flat in product(range(q), repeat=a * b):
        m = tuple(tuple(flat[i * b : (i + 1) * b]) for i in range(a))
        expected = expected_count(f, n, h1, h0, m)
        assert expected == observed[m], (q, n, h1, h0, m, expected, observed[m])
        sum_expected += expected
    assert sum_expected == count
    return {"q": q, "n": n, "a": a, "b": b,
            "rank_H1": f.rank(h1), "rank_H0": f.rank(h0),
            "frames_enumerated": count, "all_matrices_checked": q ** (a * b),
            "positive_probability_matrices": len(observed), "passed": True}


def main():
    cases = [
        (2, 1, [0], [0]),
        (2, 1, [0], [0, 1]),
        (2, 1, [0, 1], [0, 1]),
        (3, 1, [0, 1], [0, 1]),
        (4, 1, [0], [0]),
        (4, 1, [0, 1], [0, 1]),
        (2, 2, [0, 1], [0, 1]),
        (2, 2, [0, 2], [0, 2]),
        (2, 2, [0, 1], [0, 2]),
        (2, 2, [0, 1], [0, 1, 2]),
        (2, 2, [0, 2], [0, 1, 2]),
        (2, 2, [0, 1, 2], [0, 1, 2]),
        (3, 2, [0, 1], [0, 1]),
        (3, 2, [0, 2], [0, 2]),
    ]
    results = [verify_case(*case) for case in cases]
    data = {"method": "direct enumeration of all injective source frames of fixed Gram matrix",
            "extension_field": "F4 = F2[x]/(x^2+x+1)",
            "cases": results, "all_passed": True,
            "total_matrix_cases": sum(row["all_matrices_checked"] for row in results),
            "total_source_frames": sum(row["frames_enumerated"] for row in results)}
    print(json.dumps(data, indent=2))


if __name__ == "__main__":
    main()
