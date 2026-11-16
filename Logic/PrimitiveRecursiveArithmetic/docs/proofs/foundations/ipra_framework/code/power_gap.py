#!/usr/bin/env python3
"""Exact reference implementation of the superelliptic power-gap certificate.

This is not an iPRA proof checker. Its finite tests support the implementation;
the article proves the universal soundness theorem. Coefficient order is ascending.
Only Python's standard library is used.
"""
from dataclasses import dataclass, asdict
from fractions import Fraction
from itertools import product
from pathlib import Path
import json


def trim(p):
    q = list(p)
    while q and q[-1] == 0:
        q.pop()
    return q


def add(p, q):
    return trim([(p[i] if i < len(p) else 0) +
                 (q[i] if i < len(q) else 0)
                 for i in range(max(len(p), len(q)))])


def scale(c, p):
    return trim([c * x for x in p])


def mul(p, q):
    if not p or not q:
        return []
    r = [0] * (len(p) + len(q) - 1)
    for i, a in enumerate(p):
        for j, b in enumerate(q):
            r[i + j] += a * b
    return trim(r)


def poly_pow(p, m):
    q = [1]
    for _ in range(m):
        q = mul(q, p)
    return q


def evaluate(p, x):
    y = 0
    for c in reversed(p):
        y = y * x + c
    return y


@dataclass(frozen=True)
class Certificate:
    m: int
    D: int
    f: list
    A: list
    R: list

    def valid(self):
        if self.m < 2 or self.D < 1:
            return False
        if any(type(c) is not int for p in (self.f, self.A, self.R) for c in p):
            return False
        if any(trim(p) != p for p in (self.f, self.A, self.R)):
            return False
        if len(self.A) < 2 or not self.R:
            return False
        if len(self.R) - 1 >= (self.m - 1) * (len(self.A) - 1):
            return False
        return scale(self.D ** self.m, self.f) == add(poly_pow(self.A, self.m), self.R)

    def bounds(self):
        if not self.valid():
            raise ValueError("Invalid power-gap certificate")
        lower = sum(abs(a) for a in self.A[:-1])
        remainder = sum(abs(a) for a in self.R)
        H = (self.m - 1) * lower + remainder
        K = sum(abs(a) * H ** i for i, a in enumerate(self.f))
        return H, K


def complete_power(f, m, c):
    """Return (Q, certificate-or-None), where f=Q^m iff certificate is None.

    Preconditions: canonical integer f, degree=m*r>0, leading coefficient=c^m.
    The constructor uses exactly r rational coefficient steps, no unbounded search.
    """
    f = trim(f)
    if m < 2 or c == 0 or len(f) < 2 or (len(f) - 1) % m or f[-1] != c ** m:
        raise ValueError("Degree and leading coefficient do not match the input power")
    r = (len(f) - 1) // m
    q = [Fraction(0)] * r + [Fraction(c)]
    for j in range(1, r + 1):
        degree = m * r - j
        old = poly_pow(q, m)
        known = old[degree] if degree < len(old) else 0
        q[r - j] = (Fraction(f[degree]) - known) / (m * c ** (m - 1))
    D = 1
    for a in q:
        D *= a.denominator
    A = [int(D * a) for a in q]
    R = add(scale(D ** m, f), scale(-1, poly_pow(A, m)))
    if not R:
        return q, None
    cert = Certificate(m, D, f, trim(A), R)
    if not cert.valid():
        raise AssertionError("Constructor invariant failed")
    return q, cert


def integer_nth_root_floor(n, m):
    """Finite bit scan; no real arithmetic and no unknown stopping condition."""
    if n < 0 or m < 1:
        raise ValueError("Need n>=0, m>=1")
    value = 0
    for bit in range(n.bit_length(), -1, -1):
        candidate = value + (1 << bit)
        if candidate ** m <= n:
            value = candidate
    return value


def integer_power_roots(v, m):
    if v < 0 and m % 2 == 0:
        return []
    a = integer_nth_root_floor(abs(v), m)
    if a ** m != abs(v):
        return []
    if v < 0:
        return [-a]
    if m % 2 == 0 and a:
        return [-a, a]
    return [a]


def enumerate_certified(cert):
    H, _ = cert.bounds()
    return [(x, y) for x in range(-H, H + 1)
            for y in integer_power_roots(evaluate(cert.f, x), cert.m)]


def bounded_denominator_bound(cert, B):
    """Coarse uniform numerator bounds when both positive denominators <=B."""
    if B < 1 or not cert.valid():
        raise ValueError("Need a valid certificate and B>=1")
    r = len(cert.A) - 1
    lower = sum(abs(a) for a in cert.A[:-1])
    remainder = sum(abs(a) for a in cert.R)
    H = ((cert.m - 1) * B ** (r + 1) * lower +
         B ** (cert.m * (r + 1)) * remainder)
    K = B ** cert.m * sum(abs(a) * H ** i for i, a in enumerate(cert.f))
    return H, K


def validate():
    report = {"scope": "Finite exact implementation checks, not an iPRA proof", "checks": {}}
    count = 0
    for m, a, b in product(range(2, 10), range(-12, 13), range(-12, 13)):
        if b ** m != a ** m:
            assert abs(b ** m - a ** m) >= abs(a) ** (m - 1)
        count += 1
    report["checks"]["integer_gap_cases"] = count
    root_count = 0
    for m, n in product(range(2, 8), range(1001)):
        a = integer_nth_root_floor(n, m)
        assert a ** m <= n < (a + 1) ** m
        root_count += 1
    report["checks"]["root_scan_cases"] = root_count
    examples = [([1, 1, 0, 1], 3, 1),
                ([1, 1, 0, -1], 3, -1),
                ([1, 1, 0, 0, 1], 4, 1),
                ([1, 1, 0, 0, 0, 1, 1], 3, 1),
                ([2, 1, 0, 0, 4], 2, 2),
                ([1, 1, 0, 0, 0, 1], 5, 1)]
    sample_certificates = []
    sample_enumeration_count = 0
    for f, m, c in examples:
        q, cert = complete_power(f, m, c)
        assert cert is not None
        H, K = cert.bounds()
        points = enumerate_certified(cert)
        # Independent exhaustive y scan in a separate small x box, including
        # negative coordinates. It checks agreement where it is run; the paper
        # proves that the certificate's box contains every solution.
        box = min(H + 5, 30)
        ybox = 60
        brute = [(x, y) for x in range(-box, box + 1)
                 for y in range(-ybox, ybox + 1) if y ** m == evaluate(f, x)]
        expected = [(x, y) for x, y in points if abs(x) <= box and abs(y) <= ybox]
        assert brute == expected
        assert all(abs(x) <= H and abs(y) <= K for x, y in points)
        sample_enumeration_count += (2 * box + 1) * (2 * ybox + 1)
        sample_certificates.append({**asdict(cert), "H": H, "K": K, "points": points})
    report["checks"]["completion_examples"] = len(examples)
    report["checks"]["independent_point_checks"] = sample_enumeration_count
    families = []
    for m, r in product(range(3, 9), range(1, 5)):
        f = [1, 1] + [0] * (m * r - 2) + [1]
        _, cert = complete_power(f, m, 1)
        assert cert is not None and cert.bounds()[0] == 2
        points = enumerate_certified(cert)
        expected = [(-1, -1), (-1, 1), (0, -1), (0, 1)] if m % 2 == 0 else [(-1, (-1) ** r), (0, 1)]
        assert points == expected
        families.append({"m": m, "r": r, "points": points})
    report["checks"]["classified_family_instances"] = len(families)
    for m, q in [(2, [1, 2, 3]), (3, [-1, 1]), (4, [2, 1])]:
        _, cert = complete_power(poly_pow(q, m), m, q[-1])
        assert cert is None
    report["checks"]["perfect_power_branches"] = 3
    good = Certificate(3, 1, [1, 1, 0, 1], [0, 1], [1, 1])
    bad = [Certificate(1, 1, good.f, good.A, good.R),
           Certificate(3, 0, good.f, good.A, good.R),
           Certificate(3, 1, good.f, good.A, []),
           Certificate(3, 1, good.f, good.A, [1, 2]),
           Certificate(3, 1, good.f, [0, 1, 0], good.R),
           Certificate(3, 1, good.f, good.A, [1, 1, 1])]
    assert all(not c.valid() for c in bad)
    report["checks"]["invalid_certificates_rejected"] = len(bad)
    # Numerator transport tested on reduced and unreduced rational pairs.
    denom_checks = 0
    for B in range(1, 5):
        H, K = bounded_denominator_bound(good, B)
        for u, v, w, z in product(range(-5, 6), range(1, B + 1),
                                  range(-5, 6), range(1, B + 1)):
            if Fraction(w, z) ** good.m == evaluate(good.f, Fraction(u, v)):
                assert abs(u) <= H and abs(w) <= K
            denom_checks += 1
    report["checks"]["bounded_denominator_cases"] = denom_checks
    report["certificates"] = sample_certificates
    report["families"] = families
    report["passed"] = True
    return report


if __name__ == "__main__":
    data = validate()
    output = Path(__file__).resolve().parent.parent / "validation" / "power_gap_checks.json"
    output.parent.mkdir(exist_ok=True)
    output.write_text(json.dumps(data, indent=2) + "\n")
    print(json.dumps({"passed": data["passed"], "checks": data["checks"],
                      "report": str(output)}, indent=2))
