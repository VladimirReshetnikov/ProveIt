"""Finite standard-N diagnostics for J_bootstrap.tex.

Every displayed operation is built from zero, Python argument projection,
composition and successor-seeded scalar iteration.  The ordinary arithmetic
in assert statements is an independent expected-value oracle, not part of
the constructed operations.  These checks do not replace the internal
equation-induction proof in the TeX file.
"""

from functools import lru_cache
import json


def J(n, a, update):
    """Interpret one fixed scalar description: J(0,a,h)=a+1."""
    value = a + 1
    for _ in range(n):
        value = update(value)
    return value


def S(a):
    return J(0, a, lambda u: 0)


def B(n, a, b):
    return J(n, a, lambda u: b)


@lru_cache(None)
def Z(n):
    return B(n, 0, 0)


@lru_cache(None)
def plus(a, b):
    return J(b, a, S)


@lru_cache(None)
def N(n):
    return Z(J(n, 0, Z))


@lru_cache(None)
def cycle_step(u):
    return B(u, 0, B(Z(N(u)), S(0), 0))


@lru_cache(None)
def M(n):
    return cycle_step(cycle_step(J(n, 0, cycle_step)))


@lru_cache(None)
def G(n):
    return J(n, 0, lambda u: plus(u, M(S(S(u)))))


def D(a):
    return S(S(plus(a, a)))


def T(a):
    return S(S(S(S(plus(plus(a, a), a)))))


def R(a):
    return S(S(S(plus(a, a))))


@lru_cache(None)
def H(u):
    return B(Z(N(u)), G(u), u)


@lru_cache(None)
def A(x):
    return J(x, 0, R)


@lru_cache(None)
def F(x, y):
    return J(y, A(x), H)


@lru_cache(None)
def L(x, y):
    return Z(N(F(x, y)))


def K(c, u):
    return B(c, u, u)


@lru_cache(None)
def V(t, m):
    return J(t, 0, lambda u: K(Z(L(S(u), m)), u))


@lru_cache(None)
def Q(m):
    return J(m, 0, lambda u: K(Z(L(S(S(u)), m)), u))


@lru_cache(None)
def P(m):
    return B(Z(L(S(S(S(0))), m)), Q(Q(m)), L(S(S(0)), m))


def I(n, a, update):
    return P(J(n, a, lambda u: S(update(P(u)))))


def main():
    checked = 0

    def check(value):
        nonlocal checked
        assert value
        checked += 1

    for n in range(20):
        check(Z(n) == int(n == 0))
        check(N(n) == n % 2)
        check(M(n) == n % 3)
        check(G(n) == 3 * n // 2 + 1)
        check(M(G(n)) == S(N(n)))
        check(G(S(S(n))) == S(S(S(G(n)))))
        check(H(D(n)) == T(n))
        check(H(T(n)) == T(H(n)))
        check(G(T(n)) == plus(T(G(n)), N(n)))

    for x in range(5):
        for y in range(5):
            check(L(x, y) == int(x <= y))
            check(F(S(x), S(y)) == T(F(x, y)))
            check(plus(x, y) == x + y + 1)

    for n in range(6):
        check(Q(n) == max(1, n - 1))
        check(P(n) == max(0, n - 1))
        check(V(n, S(n)) == S(n))
        check(V(S(S(n)), S(n)) == S(n))

    for n in range(3):
        for a in range(3):
            check(I(n, a, S) == a + n)
            check(I(n, a, lambda u: u) == a)
            expected = a
            for _ in range(n):
                expected = int(expected == 0)
            check(I(n, a, Z) == expected)

    print(json.dumps({
        "status": "passed",
        "checks": checked,
        "scope": "Finite standard-natural-number diagnostics only",
        "P_0_through_5": [P(n) for n in range(6)],
        "A_0_through_5": [A(n) for n in range(6)],
        "G_0_through_9": [G(n) for n in range(10)]
    }, indent=2))


if __name__ == "__main__":
    main()
