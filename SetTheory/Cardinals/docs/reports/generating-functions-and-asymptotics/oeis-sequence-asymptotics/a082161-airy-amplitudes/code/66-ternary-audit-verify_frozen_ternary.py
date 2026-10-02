#!/usr/bin/env python3
"""Exact rational checks for the frozen ternary transfer boundary audit.
No third-party packages or network access are required.
"""
from fractions import Fraction as F
from random import Random


def h(r, k):
    return F(3 * k + r + 1)


def ell(r, k):
    return F(3 * k + r) + F(4, 3) + F(1, 6) * F(-1, 2) ** r * F(-1, 8) ** k


def b_entry(r, i, j):
    if i == 0:
        return {0: (4, 8, 12)[r], 1: (4, 6, 6)[r], 2: 1}.get(j, 0)
    return {i - 1: 8, i: 12, i + 1: 6, i + 2: 1}.get(j, 0)


def B(r, f, k):
    return sum(F(b_entry(r, k, j)) * f(j) for j in range(max(0, k - 1), k + 3))


def Bstar(r, f, k):
    return sum(F(b_entry(r, j, k)) * f(j) for j in range(max(0, k - 2), k + 2))


def A(f, k):
    return 2 * f(k) + f(k + 1)


def C(f, k):
    return f(k) + (2 * f(k - 1) if k else 0)


def pi(k):
    return h(0, k) * ell(0, k)


def rho(k):
    return ell(0, k) / h(0, k)


def P(f, k):
    return B(0, lambda j: h(0, j) * f(j), k) / (27 * h(0, k))


def c(k):
    b = 4 if k == 0 else 6
    return (b * ell(0, k) * h(0, k + 1) + 8 * ell(0, k + 1) * h(0, k)) / 54


def d(k):
    return ell(0, k) * h(0, k + 2) / 54


def D(k, m):
    return sum(pi(i) * F(b_entry(0, i, k)) * h(0, k) / (27 * h(0, i))
               * F(b_entry(0, i, k + m)) * h(0, k + m) / (27 * h(0, i))
               for i in range(max(0, k - 2), k + 2))


def D_formula(k, m):
    if m == 1:
        if k == 0:
            v = 16 * rho(0) + 96 * rho(1)
        elif k == 1:
            v = 4 * rho(0) + 72 * rho(1) + 96 * rho(2)
        else:
            v = 6 * rho(k - 1) + 72 * rho(k) + 96 * rho(k + 1)
    elif m == 2:
        v = (4 if k == 0 else 12) * rho(k) + 48 * rho(k + 1)
    elif m == 3:
        v = 8 * rho(k + 1)
    else:
        raise ValueError(m)
    return h(0, k) * h(0, k + m) * v / 729


for r in range(3):
    for k in range(101):
        assert B(r, lambda j: h(r, j), k) == 27 * h(r, k)
        assert Bstar(r, lambda j: ell(r, j), k) == 27 * ell(r, k)
        assert 1 <= ell(r, k) / h(r, k) <= F(3, 2)

for k in range(101):
    assert A(lambda j: h(0, j), k) == 3 * h(1, k)
    assert A(lambda j: h(1, j), k) == 3 * h(2, k)
    assert C(lambda j: h(2, j), k) == 3 * h(0, k)
    assert P(lambda _: F(1), k) == 1
    w = h(0, k) * h(0, k + 1)
    assert c(k) >= F(7, 27) * w
    assert D(k, 1) >= F(85, 486) * w
    for m in range(1, 4):
        assert D(k, m) == D_formula(k, m)
    R = (c(k) + 2 * d(k) + (2 * d(k - 1) if k else 0)) / w
    assert R <= F(53, 144)

assert c(0) == F(13, 12)
assert d(0) == F(7, 36)
assert D(0, 1) / (h(0, 0) * h(0, 1)) == F(85, 486)

rng = Random(20261002)
for N in range(1, 21):
    values = [F(rng.randint(-20, 20), rng.randint(1, 9)) for _ in range(N + 1)]
    f = lambda k: values[k] if 0 <= k <= N else F(0)
    nf = sum(pi(k) * f(k) ** 2 for k in range(N + 1))
    npf = sum(pi(k) * P(f, k) ** 2 for k in range(N + 2))
    E = sum(pi(k) * f(k) * (f(k) - P(f, k)) for k in range(N + 1))
    E_formula = sum(c(k) * (f(k + 1) - f(k)) ** 2
                    + d(k) * (f(k + 2) - f(k)) ** 2 for k in range(N + 1))
    variance_formula = sum(D_formula(k, m) * (f(k + m) - f(k)) ** 2
                           for k in range(N + 1) for m in range(1, 4))
    assert E == E_formula
    assert nf - npf == variance_formula
    for k in range(N + 1):
        assert sum(1 / (h(0, j) * h(0, j + 1)) for j in range(k, N + 1)) == F(1, 3) * (1 / h(0, k) - 1 / h(0, N + 1))
print('All exact rational checks passed: profiles, boundary rows, cycles, Markovness, form identities, lower bounds, upper comparison, resistance.')

# One-step, single-phase singular-form boundary audit.
def hh(j):
    return F(j + 1)


def ll(j):
    return F(j) + F(4, 3) + F(1, 6) * F(-1, 2) ** j


def omega(j):
    return ll(j) / hh(j)


for i in range(2, 41):
    r = (i - 1) % 3
    domain = list(range(r, i, 3))
    codomain = list(range(i % 3, i + 1, 3))
    vals = {j: F(rng.randint(-20, 20), rng.randint(1, 9)) for j in domain}
    u = lambda j: vals.get(j, F(0))
    U = lambda j: F(4 * (i - j + 3), 2 * i + j)
    alpha = 1 + F(3, 2 * i + 1)
    norm = sum(omega(j) * u(j) ** 2 for j in domain)
    normT = sum(omega(j) * (2 * u(j - 1) + u(j + 2)) ** 2 for j in codomain)
    normTi = sum(omega(j) * (U(j) * u(j - 1) + u(j + 2)) ** 2 for j in codomain)
    critical = sum(2 * omega(j) * j * (j + 3) * (u(j - 1) / j - u(j + 2) / (j + 3)) ** 2
                   for j in codomain if j > 0)
    assert 9 * norm - normT == critical
    radial = sum(hh(j) * hh(j + 3) * (u(j) / hh(j) - u(j + 3) / hh(j + 3)) ** 2 for j in domain)
    ordinary = sum((u(j + 3) - u(j)) ** 2 for j in domain) + F(3, r + 1) * u(r) ** 2
    assert radial == ordinary
    assert 2 * ordinary <= critical <= 3 * ordinary
    tail = F(0)
    for j in domain:
        delta = 1 - (U(j + 1) * ll(j + 1) + (ll(j - 2) if j >= 2 else 0)) / (3 * alpha * ll(j))
        exact = F(2 * j * (i + 1), (i + 2) * (2 * i + j + 1)) * ll(j + 1) / ll(j)
        if j >= 2:
            exact += F(1, 2 * (i + 2)) * ll(j - 2) / ll(j)
        assert delta == exact
        assert delta >= F(4 * j, 9 * i)
        tail += delta * omega(j) * u(j) ** 2
    assert 9 * alpha ** 2 * norm - normTi >= 9 * alpha ** 2 * tail
print('All one-step singular-form checks passed: weighted critical identity, exact Dirichlet boundary term, column deficit, and tail coercivity.')
