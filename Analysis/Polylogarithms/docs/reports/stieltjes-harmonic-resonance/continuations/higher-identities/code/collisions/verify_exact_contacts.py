"""Finite exact certificates for the polygamma contact formulas.

The proofs of the universal formulas are analytic and appear in collisions.tex.
This script independently checks kernel signs, confluent node normalization,
the full rationally resonant triple example, and the first exact moment rows.
"""
from itertools import combinations
from math import factorial
import json
import sympy as s

x, z, e = s.symbols('x z e', positive=True)
G = s.Symbol('gamma')
Z = {k: s.Symbol(f'zeta_{k}') for k in range(2, 20)}


def hermite(nodes, fn, remove_node_logs=False):
    table = [[fn.subs(z, a)] for a in nodes]
    if remove_node_logs:
        for row, a in zip(table, nodes):
            row[0] = row[0].subs(s.log(a), 0)
    for order in range(1, len(nodes)):
        for i in range(len(nodes) - order):
            if nodes[i] == nodes[i + order]:
                val = s.diff(fn, z, order).subs(z, nodes[i]) / factorial(order)
                if remove_node_logs:
                    val = val.subs(s.log(nodes[i]), 0)
            else:
                val = (table[i + 1][order - 1] - table[i][order - 1]) / (
                    nodes[i + order] - nodes[i])
            table[i].append(s.cancel(val))
    return table[0][-1]


def rational_coefficients(nodes, orders, degree):
    coeffs = []
    for i, (ai, hi) in enumerate(zip(nodes, orders)):
        regular = x ** degree
        for j, (aj, hj) in enumerate(zip(nodes, orders)):
            if i != j:
                regular /= (x + aj) ** hj
        for q in range(1, hi + 1):
            c = s.diff(regular, x, hi - q).subs(x, -ai) / factorial(hi - q)
            coeffs.append((i, q, c))
    return coeffs


def kernel_checks():
    rows = []
    for nodes, hs in [([2], [1]), ([2], [3]), ([2, 5], [1, 1]),
                      ([2, 5], [2, 1]), ([2, 5], [2, 2]),
                      ([2, 3, 5], [1, 1, 1]), ([2, 3, 5], [2, 1, 2])]:
        nodes = list(map(s.Integer, nodes))
        H = sum(hs)
        repeated = [a for a, h in zip(nodes, hs) for _ in range(h)]
        for d in range(H):
            coeffs = rational_coefficients(nodes, hs, d)
            reconstructed = sum(c / (x + nodes[i]) ** q for i, q, c in coeffs)
            target = x ** d / s.prod((x + a) ** h for a, h in zip(nodes, hs))
            assert s.cancel(reconstructed - target) == 0
            value = sum(-c * s.log(nodes[i]) if q == 1 else
                        c * nodes[i] ** (1 - q) / (q - 1)
                        for i, q, c in coeffs)
            dd = (-1) ** (H + d) * hermite(repeated, z ** d * s.log(z))
            assert s.simplify(value - dd) == 0
            rows.append(dict(nodes=list(map(int, nodes)), orders=hs, degree=d,
                             value=str(s.simplify(value))))
    assert s.simplify(hermite([s.Integer(2), s.Integer(2)], z * s.log(z))
                      - (s.log(2) + 1)) == 0
    return rows


def analytic_derivative(r, a, cutoff=6):
    # psi^(r)(1+a), to a degree sufficient for the worst epsilon^-6 pole.
    ans = -G if r == 0 else (-1) ** (r + 1) * factorial(r) * Z[r + 1]
    for k in range(1, cutoff + 1):
        ans += (-1) ** (r + k + 1) * factorial(r + k) / s.Integer(factorial(k)) * Z[r + k + 1] * a ** k
    return ans


def polyconv(a, b, cutoff):
    out = [s.Integer(0)] * (cutoff + 1)
    for i, ai in enumerate(a):
        for j, bj in enumerate(b):
            if i + j <= cutoff:
                out[i + j] += ai * bj
    return list(map(s.expand, out))


def resonant_triple():
    shifts = [e ** 3, e ** 2, e]
    rs = [1, 0, 0]
    rows = []
    total = s.Integer(0)
    for size in range(1, 4):
        for S in combinations(range(3), size):
            H = sum(rs[i] + 1 for i in S)
            pp = s.prod((-1) ** (rs[i] + 1) * factorial(rs[i]) for i in S)
            regular = [s.Integer(1)] + [s.Integer(0)] * (H - 1)
            for j in range(3):
                if j not in S:
                    poly = [analytic_derivative(rs[j] + d, shifts[j]) / factorial(d)
                            for d in range(H)]
                    regular = polyconv(regular, poly, H - 1)
            repeated = [shifts[i] for i in S for _ in range(rs[i] + 1)]
            contact = s.Integer(0)
            for d in range(H):
                rational_K = (-1) ** (H + d) * hermite(
                    repeated, z ** d * s.log(z), remove_node_logs=True)
                if rational_K == 0 or regular[d] == 0:
                    continue
                Kseries = s.series(rational_K, e, 0, 1).removeO()
                contact += pp * s.expand(regular[d] * Kseries).coeff(e, 0)
            contact = s.expand(contact)
            total += contact
            rows.append(dict(subset=[i + 1 for i in S], constant=str(contact)))
    baseline = Z[3] - 2 * G * Z[2]
    full = s.expand(total + baseline).subs(Z[2] ** 2, s.Rational(5, 2) * Z[4])
    expected = 4 + 2 * G - Z[2] + Z[3] + (s.Rational(9, 2) - G) * Z[4] + Z[5] - Z[6]
    assert s.expand(full - expected) == 0
    return dict(subsets=rows, full_constant=str(s.expand(full)))


def centered_moments():
    rows = []
    for N in range(2, 9):
        f = sum((-1) ** k * Z[k] * x ** k for k in range(2, N + 1))
        powers = [s.Integer(1)]
        for k in range(1, N + 1):
            powers.append(s.expand(powers[-1] * f))
            powers[-1] = sum(powers[-1].coeff(x, j) * x ** j
                             for j in range(N + 1))
        def power_coefficient(a, b):
            return s.expand(sum(s.binomial(b, k) * (-1) ** (b - k) * powers[a + k]
                                for k in range(b + 1))).coeff(x, N)
        base = -power_coefficient(0, N) / N
        values = [s.expand(base - power_coefficient(N - r, r - 1))
                  for r in range(1, N + 1)]
        assert s.expand(sum(values)) == 0
        for r in range(1, N):
            assert s.expand(values[r] - values[r - 1]
                            - power_coefficient(N - r - 1, r - 1)) == 0
        rows.append(dict(factors=N, values=list(map(str, values))))
    return rows


def run():
    report = dict(kernel_checks=kernel_checks(), resonant_triple=resonant_triple(),
                  centered_moments=centered_moments(), status='all exact assertions passed')
    print(json.dumps(report, indent=2))


if __name__ == '__main__':
    run()
