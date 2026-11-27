"""Exact finite checks for equal exponentiated circle spectra. Python 3.9+.

A candidate is an integer array indexed by powers of a primitive q-th root.
The reference test computes every Li difference in a cyclotomic power basis.
It uses neither the predicted shell decomposition nor floating-point arithmetic.
"""
from functools import lru_cache
from itertools import product
from math import gcd, lcm


@lru_cache(maxsize=None)
def cyclotomic(n):
    """Ascending coefficients of Phi_n, by exact division of x^n - 1."""
    coefficients = [-1] + [0] * (n - 1) + [1]
    for d in range(1, n):
        if n % d == 0:
            factor = cyclotomic(d)
            quotient = [0] * (len(coefficients) - len(factor) + 1)
            for i in reversed(range(len(quotient))):
                q = coefficients[i + len(factor) - 1]
                quotient[i] = q
                for j, v in enumerate(factor):
                    coefficients[i + j] -= q * v
            assert not any(coefficients)
            coefficients = quotient
    return tuple(coefficients)


@lru_cache(maxsize=None)
def root_vectors(n):
    """Power-basis coordinates of all nth roots of unity."""
    phi = cyclotomic(n)
    basis_size = len(phi) - 1
    vector = [1] + [0] * (basis_size - 1)
    vectors = []
    for _ in range(n):
        vectors.append(tuple(vector))
        top = vector[-1]
        vector = [x - top * c for x, c in zip([0] + vector[:-1], phi[:-1])]
    assert tuple(vector) == vectors[0]
    return tuple(vectors)


def character(f, j):
    values = {3: (0, 1, -1), 4: (0, 1, 0, -1)}
    return values[f][j % f]


def packet(q, f, m):
    assert q % (f * m) == 0
    stride = q // (f * m)
    return tuple(character(f, j // stride) if j % stride == 0 else 0
                 for j in range(q))


def scaled_basis(q, f, a):
    return [(q // (f * m), a // gcd(a, m), packet(q, f, m))
            for m in reversed(range(1, q // f + 1)) if q % (f * m) == 0]


def basis_accepts(array, generators):
    remainder = list(array)
    for pivot, scale, generator in generators:
        coefficient = remainder[pivot]
        if coefficient % scale:
            return False
        remainder = [u - coefficient * v for u, v in zip(remainder, generator)]
    return not any(remainder)


class FourierTest:
    def __init__(self, q, f):
        order = lcm(q, f)
        powers = root_vectors(order)
        width = len(powers[0])
        self.gauss = tuple(sum(character(f, j) * powers[j * (order // f)][i]
                               for j in range(f)) for i in range(width))
        self.axis = next(i for i, value in enumerate(self.gauss) if value)
        self.rows = []
        for n in range(1, q):
            columns = [powers[(n * j * (order // q)) % order] for j in range(q)]
            self.rows.append([tuple((1 if i == 0 else 0) - column[i]
                                    for column in columns) for i in range(width)])

    def accepts(self, array, a, b):
        for row in self.rows:
            value = tuple(sum(u * v for u, v in zip(array, entries)) for entries in row)
            k, rem = divmod(b * value[self.axis], a * self.gauss[self.axis])
            if rem or any(b * v != k * a * g for v, g in zip(value, self.gauss)):
                return False
        return True


def candidates(q, bound, skew):
    if not skew:
        for coefficients in product(range(-bound, bound + 1), repeat=q - 1):
            yield (0,) + coefficients
        return
    # Differences of real multiplicities have conjugate Fourier modes.
    # These larger tests restrict to the skew arrays of Lemma 2.1.
    width = (q - 1) // 2
    for coefficients in product(range(-bound, bound + 1), repeat=width):
        value = [0] * q
        for i, c in enumerate(coefficients, 1):
            value[i], value[-i] = c, -c
        yield tuple(value)


def bounded_test(q, f, a, den, bound, skew):
    assert gcd(a, den) == 1
    reference = FourierTest(q, f)
    generators = scaled_basis(q, f, a)
    for _, scale, generator in generators:
        assert reference.accepts(tuple(scale * i for i in generator), a, den)
        if scale > 1:
            assert not reference.accepts(tuple((scale - 1) * i for i in generator), a, den)
    hits = set()
    count = 0
    for value in candidates(q, bound, skew):
        count += 1
        direct = reference.accepts(value, a, den)
        assert direct == basis_accepts(value, generators), (q, f, a, den, value)
        if direct and any(value):
            hits.add(value)
    return count, hits


def predicted_minimizers(q, f, a):
    """Build the equality-case candidates for every possible least support exponent."""
    result = set()
    for m in range(1, q // f + 1):
        if q % (f * m):
            continue
        large = packet(q, f, m)
        if f % 2 == 0 or m % 2:
            if a % m == 0:
                for sign in (-1, 1):
                    result.add(tuple(sign * (a // m) * v for v in large))
            continue
        small = packet(q, f, m // 2)
        sign = character(f, 2)
        for x, y in product((-a, 0, a), repeat=2):
            c_numerator = y - sign * x
            if c_numerator == 0 or c_numerator % m or (2 * x) % m:
                continue
            c, e = c_numerator // m, (2 * x) // m
            result.add(tuple(c * u + e * v for u, v in zip(large, small)))
    return result


def main():
    # 'all' includes unbalanced and non-skew arrays, with no mass at 1.
    # In the skew tests each unlisted coordinate is fixed by antisymmetry.
    cases = [(3, 3, False), (4, 4, False), (5, 3, False), (5, 4, False),
             (6, 3, False), (8, 4, True), (12, 3, True), (12, 4, True)]
    totals = [0, 0]
    print(" q  f  A  B   domain   arrays  nonzero  minimum-TV  minimizers")
    for q, f, skew in cases:
        for a in (1, 2):
            previous_hits = None
            for den in (1, 3):
                size, hits = bounded_test(q, f, a, den, bound=2, skew=skew)
                if previous_hits is not None:
                    assert hits == previous_hits
                previous_hits = hits
                expected = predicted_minimizers(q, f, a)
                target = a * sum(gcd(j, f) == 1 for j in range(f))
                values = {b: sum(map(abs, b)) for b in hits}
                assert all(mass >= target for mass in values.values())
                assert {b for b, mass in values.items() if mass == target} == expected
                minimum = str(min(values.values())) if values else "-"
                print(f"{q:2} {f:2} {a:2} {den:2} {('skew' if skew else 'all'):>8}"
                      f"{size:9} {len(hits):8} {minimum:>11} {len(expected):11}")
                totals[0] += size
                totals[1] += len(hits)
    # Probe packet inclusion/exclusion at some larger support orders and numerators.
    probes = 0
    for f in (3, 4):
        for a, den in ((1, 1), (2, 3), (3, 2), (6, 5)):
            q = 12 * f
            test = FourierTest(q, f)
            for _, scale, generator in scaled_basis(q, f, a):
                for coefficient in range(-scale - 1, scale + 2):
                    probe = tuple(coefficient * v for v in generator)
                    assert test.accepts(probe, a, den) == (coefficient % scale == 0)
                    probes += 1
            for minimizer in predicted_minimizers(q, f, a):
                assert test.accepts(minimizer, a, den)
                assert sum(map(abs, minimizer)) == 2 * a
                probes += 1
    print("Bounded array/parameter tests:", totals[0])
    print("Nonzero accepted array/parameter tests:", totals[1])
    print("Additional individual packet and minimizer tests:", probes)


if __name__ == "__main__":
    main()
