#!/usr/bin/env python3
"""Finite standard-model checks, not a proof of the universal identities.

All auxiliary arithmetic functions are evaluated from the iterator definitions
in equational_predecessor.tex.  No division/modulus formula for M, G, H, L,
or P is used to compute those functions.  Python's naturals provide the model.
"""
from functools import cache
import json


def iterate(n, a, h):
    for _ in range(n):
        a = h(a)
    return a


@cache
def C(n, a, b):
    return iterate(n, a, lambda _: b)


@cache
def Z(n):
    return C(n, 1, 0)


@cache
def N(n):
    return iterate(n, 0, Z)


@cache
def j(u):
    return Z(u) + 2 * N(u)


@cache
def M(n):
    return iterate(n, 0, j)


@cache
def G(n):
    return iterate(n, 0, lambda u: u + M(u) + 1)


@cache
def H(u):
    return C(N(u), G(u), u)


@cache
def A(x):
    return iterate(x, 1, lambda u: 2 * u)


@cache
def L(x, y):
    return N(iterate(y, A(x), H))


@cache
def B(m, u):
    return C(L(u + 1, m), u, u + 1)


@cache
def W(t, m):
    return iterate(t, 0, lambda u: B(m, u))


@cache
def V(t, m):
    return iterate(t, 0, lambda u: C(L(u + 2, m + 1), u, u + 1))


@cache
def P(m):
    return iterate(m, 0, lambda u: C(L(u + 2, m), u, u + 1))


def main():
    checks = 0

    def eq(a, b):
        nonlocal checks
        assert a == b, (a, b)
        checks += 1

    for n in range(7):
        b = N(n)
        eq(b + Z(b), 1)
        eq(Z(Z(b)), b)
        eq(N(n + 2), b)
        eq(N(2 * n), 0)
        eq(N(2 * n + 1), 1)
        eq(N(3 * n), b)
        eq(C(b, j(b), j(j(b))), Z(b))
        eq(M(G(n)), b)
        eq(G(n + 1), G(n) + b + 1)
        eq(G(n + 2), G(n) + 3)
        eq(G(2 * n), 3 * n)
        eq(G(3 * n), 3 * G(n) + b)
        eq(H(2 * n), 3 * n)
        eq(H(3 * n), 3 * H(n))
        eq(L(0, n), 1)
        eq(L(n + 1, 0), 0)
        eq(L(n + 1, n), 0)
        eq(W(n, n), n)
        eq(W(n + 1, n), n)
        eq(P(n + 1), n)
        for g in range(7):
            eq(M(g + b + 1), C(b, j(M(g)), j(j(M(g)))))
        for a in range(4):
            for c in range(4):
                eq(C(b, 3 * a + b, 3 * c), 3 * C(b, a, c))

    for x in range(6):
        for y in range(6):
            eq(L(x + 1, y + 1), L(x, y))
            eq(B(y + 1, x + 1), 1 + B(y, x))
            eq(W(x + 1, y + 1), 1 + W(x, y))
            eq(V(x, y), W(x, y))
    eq(P(0), 0)
    eq(H(1), 1)
    print(json.dumps({
        "status": "passed",
        "equality_checks": checks,
        "main_range": "0..6 inclusive",
        "two_parameter_range": "0..5 inclusive",
        "predecessor_values_0_to_7": [P(n) for n in range(8)],
        "scope": "Finite standard-model evaluation only; universal proofs are in the LaTeX appendix."
    }, indent=2))


if __name__ == "__main__":
    main()
