"""Independent finite exact fixtures for the planar-kernel audit.

This script imports only the standard library and reads no source packet or
upstream program. It does not establish the universal mathematical claims.
All checks explicitly raise on failure and remain enabled under python -O.
"""

from fractions import Fraction as F
from math import gcd, lcm
import json


def require(truth, label):
    if not truth:
        raise RuntimeError(label)


def matrix(a, b, c, d):
    return ((F(a), F(b)), (F(c), F(d)))


I = matrix(1, 0, 0, 1)


def mm(a, b):
    return tuple(tuple(sum(a[i][k] * b[k][j] for k in (0, 1))
                       for j in (0, 1)) for i in (0, 1))


def mv(a, x):
    return tuple(sum(a[i][j] * x[j] for j in (0, 1)) for i in (0, 1))


def transpose(a):
    return tuple(zip(*a))


def inverse(a):
    d = a[0][0] * a[1][1] - a[0][1] * a[1][0]
    require(d != 0, "matrix inverse")
    return matrix(a[1][1] / d, -a[0][1] / d,
                  -a[1][0] / d, a[0][0] / d)


def power(a, n):
    if n < 0:
        return power(inverse(a), -n)
    z = I
    while n:
        if n % 2:
            z = mm(z, a)
        a = mm(a, a)
        n //= 2
    return z


def dot(a, b):
    return sum(x * y for x, y in zip(a, b))


def quad(q, x):
    return dot(x, mv(q, x))


def trace(a):
    return a[0][0] + a[1][1]


def hit_backward(a, p, x):
    # This is written afresh from the reviewed denominator argument.
    am_p = mv(inverse(a), p)
    basis = matrix(p[0], am_p[0], p[1], am_p[1])
    y = mv(inverse(basis), x)
    if y == (F(1), F(0)):
        return 0
    t = trace(a)
    q = t.denominator
    require(q >= 2, "infinite-order rational trace")
    d = lcm(*(v.denominator for v in y))
    m = 0
    while d > 1 and d % q == 0:
        d //= q
        m += 1
    if d != 1:
        return None
    c = matrix(0, -1, 1, t)
    if mv(power(c, m + 1), (F(1), F(0))) == y:
        return m + 1
    return None


def elliptic_fixtures():
    metrics = contacts = denominators = orbit_decisions = 0
    changes = (I, matrix(2, 1, 3, 2),
               matrix(F(1, 2), 2, F(-1, 3), F(3, 5)))
    for q in range(2, 19):
        for numerator in range(-2 * q + 1, 2 * q):
            if gcd(numerator, q) != 1:
                continue
            t = F(numerator, q)
            c = matrix(0, -1, 1, t)
            h = matrix(1, t / 2, t / 2, 1)
            for n in range(1, 20):
                v = mv(power(c, n), (F(1), F(0)))
                require(lcm(*(z.denominator for z in v)) == q ** (n - 1),
                        "denominator growth")
                denominators += 1
            # Rational conjugations exercise bases with unrelated denominators.
            for change in changes:
                ci = inverse(change)
                a = mm(mm(change, c), ci)
                metric = mm(mm(transpose(ci), h), ci)
                require(mm(mm(transpose(a), metric), a) == metric,
                        "preserved rational metric")
                require(metric[0][0] > 0 and
                        metric[0][0] * metric[1][1] > metric[0][1] ** 2,
                        "positive definite metric")
                metrics += 1
                p = mv(change, (F(1), F(0)))
                row = mv(metric, p)
                support = dot(row, mv(inverse(metric), row))
                contact = tuple(z / support for z in mv(inverse(metric), row))
                require(support == 1 and contact == p and quad(metric, p) == 1,
                        "rational tangency contact")
                contacts += 1
                for n in (-7, -3, -1, 0, 1, 2, 6):
                    x = mv(power(a, n), p)
                    actual = hit_backward(a, p, x)
                    expected = -n if n <= 0 else None
                    require(actual == expected, "forward/backward orbit distinction")
                    orbit_decisions += 1
    return dict(metric_identities=metrics, contact_identities=contacts,
                denominator_instances=denominators,
                forward_backward_decisions=orbit_decisions)


def mixed_fixtures():
    count = 0
    # The oblique guard detects admitted limit equality at x=1,y<0.
    rows = (((F(1), F(0)), F(2)), ((F(-1), F(0)), F(2)),
            ((F(0), F(1)), F(1)), ((F(0), F(-1)), F(1)),
            ((F(1), F(1)), F(1)))
    values = (F(-3, 2), F(-1), F(-1, 2), F(0), F(1, 2), F(1), F(3, 2))
    for epsilon in (-1, 1):
        for mu in (F(-3, 4), F(-1, 2), F(0), F(1, 3), F(3, 4)):
            a = matrix(epsilon, 0, 0, mu)
            for xx in values:
                for yy in values:
                    x = (xx, yy)
                    if mu:
                        formula = all(dot(row, mv(power(a, j), x)) < bound
                                      and row[0] * epsilon ** j * xx <= bound
                                      for row, bound in rows for j in (0, 1))
                    else:
                        formula = all(dot(row, mv(power(a, j), x)) < bound
                                      for row, bound in rows for j in (0, 1, 2))
                    prefix = all(dot(row, mv(power(a, j), x)) < bound
                                 for row, bound in rows for j in range(81))
                    require(formula == prefix, "mixed finite fixture")
                    count += 1
    # A separate asymmetric polygon makes the zero-stable time-2 guard essential.
    z = (F(1), F(-1, 2))
    def inside(v):
        return -2 < v[0] < F(3, 2) and -1 < v[1] < 1 and sum(v) < 1
    a = matrix(-1, 0, 0, 0)
    require(inside(z) and inside(mv(a, z)) and not inside(mv(power(a, 2), z)),
            "zero stable eigenvalue attained limit")
    return dict(rational_grid_points=count, zero_stable_witness=True)


def stable_fixtures():
    records = []
    matrices = (matrix(0, 1, 0, 0), matrix(F(-1, 2), 7, 0, F(-1, 2)),
                matrix(0, F(1, 4), 1, F(1, 4)),
                matrix(0, F(-1, 4), 1, F(1, 4)))
    def norm(a):
        return max(sum(abs(x) for x in row) for row in a)
    for a in matrices:
        k = 1
        while norm(power(a, k)) > F(1, 2):
            k += 1
            require(k < 200, "fixture contraction bound")
        ca = max(norm(power(a, j)) for j in range(k))
        q = 0
        while ca * F(1, 2) ** q >= F(1, 4):
            q += 1
        cutoff = q * k
        require(all(norm(power(a, n)) < F(1, 4)
                    for n in range(cutoff, cutoff + 4 * k)),
                "contraction-tail norm fixtures")
        records.append(dict(k=k, C=str(ca), cutoff=cutoff))
    return records


def facet_fixtures():
    records = []
    for m in (4, 6, 7, 13, 31, 127):
        lam = F(m - 1, m)
        delta = 1 - lam
        limit = (m - 1) // 2
        xs = [lam ** (-n) * (1 - n * delta / lam) for n in range(limit + 1)]
        intercepts = [None] + [lam ** (1 - n) / n for n in range(1, 4 * m + 1)]
        for n in range(1, limit + 1):
            require(xs[n] - xs[n - 1] == -n * delta ** 2 * lam ** (-n - 1),
                    "adjacent-facet abscissae")
            for ratio in (F(1, 3), F(2, 3)):
                x = ratio * xs[n] + (1 - ratio) * xs[n - 1]
                y = intercepts[n] - lam * x / n
                require(0 < x < 1 and 0 < y < 1, "facet inside initial square")
                require(lam ** n * x + n * lam ** (n - 1) * y == 1,
                        "exact active guard")
                require(all(y < intercepts[j] - lam * x / j
                            for j in range(1, 4 * m + 1) if j != n),
                        "other sampled time guards strict")
        records.append(dict(M=m, distinct_lines=limit, interior_points=2 * limit))
    return records


if __name__ == '__main__':
    print(json.dumps(dict(status='passed', elliptic=elliptic_fixtures(),
                          mixed=mixed_fixtures(), stable=stable_fixtures(),
                          facets=facet_fixtures(),
                          scope='New independent finite exact fixtures, not a universal proof.'),
                     indent=2))
