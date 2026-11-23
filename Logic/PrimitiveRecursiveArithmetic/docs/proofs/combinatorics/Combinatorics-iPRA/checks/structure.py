"""Finite regression checks for the incidence, order, and geometry chapters."""

from collections import Counter
from fractions import Fraction
from itertools import combinations, permutations, product
from math import comb, factorial


def test_kirkman():
    # Positions 0..6 stand for A_i, 7..13 for B_i; 14 is infinity.
    starter = [(14, 0, 7), (1, 2, 4), (3, 8, 12), (5, 11, 13), (6, 9, 10)]
    frequencies = Counter()
    for day in range(7):
        rows = [
            tuple(14 if i == 14 else i // 7 * 7 + (i + day) % 7 for i in row)
            for row in starter
        ]
        assert sorted(i for row in rows for i in row) == list(range(15))
        for row in rows:
            frequencies.update(combinations(sorted(row), 2))
    assert frequencies == Counter(combinations(range(15), 2))


def test_planes():
    for p in (2, 3, 5, 7):
        finite_count = p * p
        lines = []
        for slope in range(p):
            for intercept in range(p):
                points = {p * x + (slope * x + intercept) % p for x in range(p)}
                lines.append(points | {finite_count + slope})
        for x in range(p):
            lines.append({p * x + y for y in range(p)} | {finite_count + p})
        lines.append(set(range(finite_count, finite_count + p + 1)))
        v = p * p + p + 1
        assert len(lines) == v and all(len(line) == p + 1 for line in lines)
        frequencies = Counter(pair for line in lines for pair in combinations(sorted(line), 2))
        assert frequencies == Counter(combinations(range(v), 2))
        assert all(len(first & second) == 1 for first, second in combinations(lines, 2))


def test_perfect_codes():
    for r in (2, 3, 4):
        n = 2**r - 1

        def syndrome(word):
            result = 0
            for i in range(n):
                if word >> i & 1:
                    result ^= i + 1
            return result

        fibers = Counter()
        for word in range(2**n):
            error = syndrome(word)
            corrected = word ^ (1 << (error - 1)) if error else word
            assert syndrome(corrected) == 0 and (corrected ^ word).bit_count() <= 1
            fibers[corrected] += 1
        assert len(fibers) == 2 ** (n - r) and set(fibers.values()) == {n + 1}
        assert min(word.bit_count() for word in fibers if word) == 3


def test_set_bounds():
    # Exhaustively inspect all 65,536 subfamilies of the 4-cube.
    n = 4
    weights = [factorial(a.bit_count()) * factorial(n - a.bit_count()) for a in range(2**n)]
    for family in range(1 << (2**n)):
        selected = [a for a in range(2**n) if family >> a & 1]
        # Numeric order is a linear extension of mask inclusion.
        heights = {}
        for a in selected:
            heights[a] = 1 + max((h for b, h in heights.items() if a & b == b), default=0)
        r = max(heights.values(), default=0)
        assert sum(weights[a] for a in selected) <= r * factorial(n)
        assert len(selected) <= sum(sorted((comb(n, j) for j in range(n + 1)), reverse=True)[:r])
        if r == 1 and len(selected) == comb(n, n // 2):
            assert all(a.bit_count() == n // 2 for a in selected)
    # Per-circle lemma behind EKR, with both empty families and boundary n=2k.
    for n in range(2, 11):
        for k in range(1, n // 2 + 1):
            arcs = [sum(1 << ((i + offset) % n) for offset in range(k)) for i in range(n)]
            for subset in combinations(arcs, k + 1):
                assert any(a & b == 0 for a, b in combinations(subset, 2))


def test_birkhoff():
    for n in (1, 2, 3, 4):
        perms = list(permutations(range(n)))
        # Include the uniform point, individual vertices, and weighted mixtures.
        for inputs in ([p] for p in perms):
            check_decomposition(n, perms, inputs)
        check_decomposition(n, perms, perms)
        for i, p in enumerate(perms):
            check_decomposition(n, perms, [p, p, perms[-i - 1], perms[(3 * i + 1) % len(perms)]])


def check_decomposition(n, perms, inputs):
    counts = [[0] * n for _ in range(n)]
    for p in inputs:
        for i, j in enumerate(p):
            counts[i][j] += 1
    residual = [row[:] for row in counts]
    output = []
    while sum(residual[0]):
        p = next(p for p in perms if all(residual[i][p[i]] for i in range(n)))
        weight = min(residual[i][p[i]] for i in range(n))
        for i, j in enumerate(p):
            residual[i][j] -= weight
        output.append((p, weight))
    assert len(output) <= n**2 and sum(w for p, w in output) == len(inputs)
    rebuilt = [[0] * n for _ in range(n)]
    for p, w in output:
        for i, j in enumerate(p):
            rebuilt[i][j] += w
    assert rebuilt == counts


def test_permutohedron():
    for n in range(1, 6):
        perms = list(permutations(range(n)))
        counts = Counter()
        faces = set()
        for k in range(1, n + 1):
            for order in product(range(k), repeat=n):
                if len(set(order)) != k:
                    continue
                values = [sum(a * b for a, b in zip(order, vertex)) for vertex in perms]
                best = max(values)
                face = tuple(i for i, value in enumerate(values) if value == best)
                assert face not in faces
                faces.add(face)
                counts[n - k] += 1
        assert counts[0] == factorial(n)
        assert n == 1 or counts[n - 2] == 2**n - 2
        assert sum((-1) ** j * count for j, count in counts.items()) == 1


def test_kissing():
    # Double all coordinates, keeping the arithmetic integral.
    roots = []
    for i, j in combinations(range(8), 2):
        for sign_i, sign_j in product((-2, 2), repeat=2):
            v = [0] * 8
            v[i], v[j] = sign_i, sign_j
            roots.append(v)
    roots.extend(s for s in product((-1, 1), repeat=8) if s.count(-1) % 2 == 0)
    assert len(roots) == 240
    assert all(sum(x * x for x in v) == 8 for v in roots)
    assert min(sum((x - y) ** 2 for x, y in zip(v, w)) for v, w in combinations(roots, 2)) == 8
    for i in range(25):
        for j in range(i, 25):
            a, b = Fraction(i, 16), Fraction(j, 16)
            lhs = 4 * (1 + a * b) ** 2 - (1 + a**2) * (1 + b**2)
            rhs = 3 - b**2 + a * (8 * b - a) + 3 * a**2 * b**2
            assert lhs == rhs > 0


if __name__ == "__main__":
    for check in (
        test_kirkman, test_planes, test_perfect_codes, test_set_bounds,
        test_birkhoff, test_permutohedron, test_kissing,
    ):
        check()
        print(check.__name__, "passed")
