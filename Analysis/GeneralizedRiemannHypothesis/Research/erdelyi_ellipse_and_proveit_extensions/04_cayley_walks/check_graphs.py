"""Exact symbolic and exhaustive checks of connected equality cases on listed hosts.

Python 3.10+, with SymPy. Orbit basis spectra are computed by polynomial
remainder in Q[X]/Phi_L; the equality classifier is used only for comparison.
"""
from collections import Counter, deque
from itertools import product
from functools import cache
from math import gcd, lcm, prod
from sympy import Poly, cyclotomic_poly, kronecker_symbol, symbols


def check(moduli, f):
    points = list(product(*(range(n) for n in moduli)))
    size = len(points)
    exponent = lcm(*moduli)
    assert exponent % f == 0
    chi = [int(kronecker_symbol(-f, a)) for a in range(f)]
    phi = sum(abs(c) for c in chi)
    units = [v for v in range(exponent) if gcd(v, exponent) == 1]
    unseen = set(points)
    orbits = []
    while unseen:
        base = min(unseen)
        orbit = {}
        consistent = True
        for v in units:
            x = tuple(v * t % n for t, n in zip(base, moduli))
            if x in orbit and orbit[x] != chi[v % f]:
                consistent = False
            orbit[x] = chi[v % f]
        unseen.difference_update(orbit)
        if consistent:
            orbits.append(orbit)

    X = symbols("X")
    modulus = Poly(cyclotomic_poly(exponent, X), X)

    @cache
    def power(k):
        return Poly(X**k, X).rem(modulus)

    tau = sum((chi[a] * power(a*exponent//f) for a in range(f)), Poly(0, X))
    reps = [min(orbit) for orbit in orbits]
    lengths = [len(orbit) for orbit in orbits]
    matrix = []
    for freq in points:
        row = []
        for orbit in orbits:
            val = Poly(0, X)
            for point, weight in orbit.items():
                k = sum(x*y*(exponent//n) for x, y, n in zip(point, freq, moduli)) % exponent
                val += weight * power(k)
            coeff = val.nth(tau.degree()) / tau.LC()
            assert coeff.is_Integer and val == coeff*tau
            row.append(int(coeff))
        matrix.append(tuple(row))
    # Equal or opposite rows give identical conditions on absolute values.
    matrix = {min(row, tuple(-c for c in row)) for row in matrix}

    @cache
    def connected(subset):
        # The occupied orbits consist of multiples of their representatives.
        steps = [reps[i] for i in subset]
        group = {points[0]}
        new = deque(group)
        while new:
            x = new.popleft()
            for step in steps:
                y = tuple((u+v) % n for u, v, n in zip(x, step, moduli))
                if y not in group:
                    group.add(y)
                    new.append(y)
        return len(group) == size

    actual = set()
    for symbol in product((-1, 0, 1), repeat=len(reps)):
        subset = tuple(i for i, s in enumerate(symbol) if s)
        supp = sum(lengths[i] for i in subset)
        if not subset or supp % phi or not connected(subset):
            continue
        a = supp // phi
        if all(sum(s*c for s, c in zip(symbol, row)) in (-a, 0, a) for row in matrix):
            actual.add(symbol)

    def maps(m):
        for coeff in product(*([a for a in range(m) if n*a % m == 0] for n in moduli)):
            yield [sum(a*x for a, x in zip(coeff, point)) % m for point in points]

    index = [points.index(x) for x in reps]
    predicted = set()
    def record(values):
        symbol = tuple(values[i] for i in index)
        predicted.add(symbol)
        predicted.add(tuple(-v for v in symbol))

    binary = list(maps(2)) if f % 2 else [[0]*size]
    for j in maps(f):
        if len(set(j)) < f:
            continue
        for eps in binary:
            base = [(-1)**s * chi[t] for s, t in zip(eps, j)]
            record(base)
            if f % 2:
                for eta in binary:
                    if any(eta):
                        record([c*w for c, w in zip(base, eta)])
        if f % 8 == 0:
            for h in maps(4):
                if len(set(zip(j, h))) == 4*f:
                    record([chi[t] if w in (0, t % 4) else 0 for t, w in zip(j, h)])
    assert actual == predicted, (moduli, f, actual ^ predicted)
    spacings = Counter(sum(l for l, c in zip(lengths, symbol) if c)//phi for symbol in actual)
    print(f"G={moduli!s:13} f={f:2}  orbit assignments={3**len(orbits):5}  "
          f"connected equality symbols by a: {dict(sorted(spacings.items()))}")


if __name__ == "__main__":
    for moduli, f in [
        ((3, 3), 3), ((3, 6), 3), ((4, 4), 4), ((8,), 8), ((8, 4), 8),
        ((8, 4, 2), 8), ((7, 7), 7), ((3, 15), 15), ((30,), 15),
        ((4, 20), 20), ((8, 12), 24), ((8, 24), 24),
    ]:
        check(moduli, f)
