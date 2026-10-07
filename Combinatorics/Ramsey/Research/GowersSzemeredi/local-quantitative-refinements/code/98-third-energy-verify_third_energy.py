"""Independent exact bounded checks accompanying third_energy_body.tex.

Run with Python 3. No third-party packages are required. The certificate
generator and stored JSON must be beside this file.
"""

from collections import Counter
from fractions import Fraction
from itertools import product
from math import comb
from pathlib import Path
import json

from small_cyclic_m3 import classify, vectors


def direct_inventory(n):
    """Use ordered triples directly, rather than unordered triple types."""
    triples = list(product(range(n), repeat=3))
    counts = [tuple(t.count(j) for j in range(n)) for t in triples]
    weights = Counter()
    zero = 0
    for i, left in enumerate(triples):
        for j, right in enumerate(triples):
            if (sum(left) - sum(right)) % n:
                continue
            c = tuple(counts[i][k] - counts[j][k] for k in range(1, n))
            v = (sum(k * c[k - 1] for k in range(1, n)) // n,) + c[1:]
            if not any(v):
                zero += 1
            else:
                if next(x for x in v if x) < 0:
                    v = tuple(-x for x in v)
                weights[v] += 1
    return weights, zero


def energy_on_cycle(values, modulus, m=3, target_modulus=None):
    histogram = Counter()
    for t in product(range(len(values)), repeat=m):
        s = sum(t) % modulus
        a = sum(values[i] for i in t)
        if target_modulus is not None:
            a %= target_modulus
        histogram[s, a] += 1
    return sum(c * c for c in histogram.values())


def integer_convolution(left, right):
    out = Counter()
    for x, a in left.items():
        for y, b in right.items():
            out[x + y] += a * b
    return out


def power(histogram, m, add):
    out = Counter({(0, 0, 0): 1})
    for _ in range(m):
        new = Counter()
        for x, a in out.items():
            for y, b in histogram.items():
                new[add(x, y)] += a * b
        out = new
    return out


def main():
    here = Path(__file__).resolve().parent
    stored = json.loads((here / "small_cyclic_m3.json").read_text())
    recomputed = [classify(n) for n in range(2, 6)]
    # JSON normalization turns tuples in the generator result into lists.
    assert json.loads(json.dumps(recomputed)) == stored
    for n in range(2, 6):
        assert direct_inventory(n) == vectors(n)

    examples = [
        (2, [0, 1], None, 20),
        (3, [0, 0, 1], 2, 143),
        (4, [0, 0, 1, 1], 2, 640),
        (5, [0, 0, 0, 1, 1], 2, 1793),
    ]
    for n, values, target, expected in examples:
        assert energy_on_cycle(values, n, target_modulus=target) == expected

    # Check the exact four-point coefficient identity over several torsion
    # targets. The numerator is counted using actual ordered triples.
    triples = list(product(range(4), repeat=3))
    for q in range(2, 12):
        for a, m in product(range(q), repeat=2):
            values = [0, 0, a, (a + m) % q]
            hist = Counter((sum(t), sum(values[i] for i in t) % q)
                           for t in triples)
            direct = sum(c * c for c in hist.values())
            formula = (256 + 144 * (m == 0) + 84 * (a == 0)
                       + 84 * ((a - m) % q == 0)
                       + 6 * ((a + m) % q == 0)
                       + 6 * ((a - 2 * m) % q == 0))
            assert direct == formula
            if m:
                assert direct <= 346
    expected_denominators = {7: 622, 8: 592, 9: 582, 10: 580}
    for n, expected in expected_denominators.items():
        hist = Counter(sum(t) % n for t in triples)
        assert sum(c * c for c in hist.values()) == expected

    # Check the interval polynomial and adjacent-shift correlation exactly.
    for n in range(1, 16):
        interval = Counter({i: 1 for i in range(n)})
        triple = integer_convolution(integer_convolution(interval, interval), interval)
        u = sum(c * c for c in triple.values())
        c = sum(v * triple.get(i - 1, 0) for i, v in triple.items())
        assert u == Fraction(11 * n**5 + 5 * n**3 + 4 * n, 20)
        assert u - c == Fraction(n**3 + n, 2)
        ratio = Fraction(20 * u, 20 * u + 12 * c)
        exact = Fraction(5 * (11 * n**4 + 5 * n**2 + 4),
                         88 * n**4 + 10 * n**2 + 2)
        assert ratio == exact
        assert ratio - Fraction(5, 8) == Fraction(
            75 * (n**2 + 1), 8 * (44 * n**4 + 5 * n**2 + 1))

    # The C2 source gives exact finite witnesses for both higher-energy
    # formulas, with target C4 (defect order 2) and Z (infinite defect).
    for m in range(2, 9):
        denominator = 2**(2 * m - 1)
        n2 = energy_on_cycle([0, 1], 2, m, 4)
        ninf = energy_on_cycle([0, 1], 2, m, None)
        assert Fraction(n2, denominator) == Fraction(1, 2) + Fraction(1, 2**m)
        assert Fraction(ninf, denominator) == Fraction(comb(2 * m, m), denominator)

    # Independently convolve the graph of q(s,t)=s*t on F2^2 with unequal
    # positive integer weights. This tests the all-order inequality and
    # the stated equality case on a finite exact family.
    add = lambda x, y: tuple(a ^ b for a, b in zip(x, y))
    points = list(product(range(2), repeat=2))
    for m in range(2, 6):
        bound = Fraction(1, 2) + Fraction(1, 2**(2 * m - 1))
        for ws in product(range(1, 4), repeat=4):
            graph = Counter({(s, t, s * t): w
                             for (s, t), w in zip(points, ws)})
            convolved = power(graph, m, add)
            numerator = sum(c * c for c in convolved.values())
            projected = Counter()
            for (s, t, _), c in convolved.items():
                projected[s, t] += c
            denominator = sum(c * c for c in projected.values())
            ratio = Fraction(numerator, denominator)
            assert ratio >= bound
            assert (ratio == bound) == (len(set(ws)) == 1)

    print("PASS: certificate regeneration and independent ordered-triple inventories")
    print("PASS: all small-cycle attaining maps and the four-point torsion identity")
    print("PASS: wrapped denominators and exact interval formula")
    print("PASS: all-order C2 witnesses and bounded weighted Jensen tests")


if __name__ == "__main__":
    main()
