"""Exact checks of the sparse-polynomial staircase and closed-disk determinant rule."""
from fractions import Fraction
from itertools import combinations, combinations_with_replacement
from math import comb, factorial, gcd, lcm
from functools import reduce


def valuation(n, p):
    if n == 0:
        raise ValueError("valuation of zero")
    if isinstance(n, Fraction):
        return valuation(n.numerator, p) - valuation(n.denominator, p)
    count = 0
    while n % p == 0:
        n //= p
        count += 1
    return count


def digit_sum(n, p):
    count = 0
    while n:
        n, d = divmod(n, p)
        count += d
    return count


def multiply_linear(poly, x):
    return [a - x * b for a, b in zip([0] + poly, poly + [0])]


def integer_witness(p, i):
    big, small = p + i + 1, i + 1
    support = [j * p for j in range(big)] + [1 + j * p for j in range(small)]
    moments = [0 if k < big else comb(k, i) % p for k in range(len(support))]
    coeff = []
    for n in support:
        basis, den = [1], 1
        for m in support:
            if m != n:
                basis = multiply_linear(basis, m)
                den *= n - m
        coeff.append(Fraction(sum(a * b for a, b in zip(basis, moments)), den))
    denominator = lcm(*(x.denominator for x in coeff))
    values = [int(x * denominator) for x in coeff]
    divisor = reduce(gcd, values)
    return dict(zip(support, [x // divisor for x in values]))


def shifted(poly):
    result = [0] * (max(poly) + 1)
    for n, c in poly.items():
        # Coefficients of (1+Y)^n, generated without repeated factorials.
        binomial = 1
        for k in range(n + 1):
            result[k] += c * binomial
            binomial = binomial * (n - k) // (k + 1)
    return result


def open_roots(poly, p):
    heights = [(valuation(c, p) * (p - 1) + k, k)
               for k, c in enumerate(shifted(poly)) if c]
    height, first = min(heights)
    return first, height


def poly_trim(a):
    while a and not a[-1]:
        a.pop()
    return a


def squarefree_mod(poly, q):
    degree = max(poly)
    a = [poly.get(i, 0) % q for i in range(degree + 1)]
    if not a[-1]:
        return False
    b = poly_trim([i * a[i] % q for i in range(1, degree + 1)])
    while b:
        inv = pow(b[-1], -1, q)
        while len(a) >= len(b):
            k, c = len(a) - len(b), a[-1] * inv % q
            for i, x in enumerate(b):
                a[k + i] = (a[k + i] - c * x) % q
            poly_trim(a)
        a, b = b, a
    return len(a) == 1


def simple_witness(p, i):
    poly = integer_witness(p, i)
    count, height = open_roots(poly, p)
    assert count == p * p + i
    unit = p ** max(1, 1 + height // (p - 1))
    for c in range(1, 25):
        test = {**poly, 0: poly[0] + unit * c}
        for q in [23, 29, 31, 37, 41, 43, 47, 53]:
            if q != p and squarefree_mod(test, q):
                assert open_roots(test, p)[0] == count
                return test, q
    raise AssertionError("no squarefree certificate found")


def determinant(rows):
    a = [[Fraction(v) for v in row] for row in rows]
    d = Fraction(1)
    for j in range(len(a)):
        k = next((k for k in range(j, len(a)) if a[k][j]), None)
        if k is None:
            return 0
        if k != j:
            a[k], a[j] = a[j], a[k]
            d = -d
        d *= a[j][j]
        for k in range(j + 1, len(a)):
            q = a[k][j] / a[j][j]
            for m in range(j + 1, len(a)):
                a[k][m] -= q * a[j][m]
    return d


def closed_by_minors(E, p, r, moments):
    """Moments: truncated exponential; otherwise entire finite binomial matrix."""
    t = len(E)
    if moments:
        D = max(digit_sum(k, p) for k in range(t))
        A = max(1, (D - 1 + p - 2) // (p - 1))
        h = 0
        while p ** h < t:
            h += 1
        K = max(t - 1, (D - 1) * p ** (h + A - 1))
        # Discard indices whose Archimedean-free weights exceed every early weight.
        weights = [r * k - valuation(factorial(k), p) for k in range(K + 1)]
        idx = [k for k, w in enumerate(weights) if k < t or w <= max(weights[:t])]
        cols = [[n ** k for n in E] for k in idx]
    else:
        idx = list(range(max(E) + 1))
        weights = [r * k for k in idx]
        cols = [[comb(n, k) if n >= k else 0 for n in E] for k in idx]
    best, endpoint = None, None
    for J in combinations(range(len(idx)), t):
        det = determinant([cols[j] for j in J])
        if det:
            w = valuation(det, p) + sum(weights[idx[j]] for j in J)
            if best is None or w < best:
                best, endpoint = w, idx[J[-1]]
            elif w == best:
                endpoint = max(endpoint, idx[J[-1]])
    return endpoint


def add_to_basis(vector, pivots, p):
    for j in range(len(vector)):
        v = vector[j] % p
        if not v:
            continue
        if j not in pivots:
            scalar = pow(v, -1, p)
            pivots[j] = [scalar * x % p for x in vector]
            return True
        vector = [(x - v * y) % p for x, y in zip(vector, pivots[j])]
    return False


def mod_p_check(residues, p):
    """Near-boundary positive index candidates, computed via the jet algebra."""
    t = len(residues)
    D = max(digit_sum(k, p) for k in range(t))
    assert D <= p
    K = max(t - 1, (D - 1) * p ** 3)
    rows = [(a, b) for a in range(p) for b in range(residues.count(a))]
    pivots, accepted = {}, []
    for k in sorted(range(K + 1), key=lambda z: (digit_sum(z, p), z)):
        v = [comb(k, b) * pow(a, k - b, p) % p if k >= b else 0 for a,b in rows]
        if add_to_basis(v, pivots, p):
            accepted.append(k)
        if len(pivots) == t:
            break
    # If the least possible vanishing-order baseline is larger, include it.
    return max(t - 1, max(accepted))


def main():
    checks = 0
    for p in [2, 3, 5]:
        maxima = []
        for t in range(p + 2, 2 * p + 2):
            best = 0
            for R in combinations_with_replacement(range(p), t):
                best = max(best, mod_p_check(R, p))
                checks += 1
            assert best == p * p + (t - p - 2) // 2, (p,t,best)
            maxima.append(best)
        print("p =", p, "exhaustive single-layer rank maxima:", maxima)
    print("residue multisets tested:", checks)
    n = 0
    for p in [2, 3, 5, 7, 11, 13, 17]:
        for i in range((p - 1) // 2 + 1):
            poly, q = simple_witness(p, i)
            assert all(poly.values())
            n += 1
            if (p, i) == (5, 2):
                print("p=5, i=2 witness:", sorted(poly.items()))
                print("open Newton index:", open_roots(poly, p)[0],
                      "squarefree certificate prime:", q)
        print("p =", p, "simple witness open counts:",
              list(range(p*p,p*p+(p-1)//2+1)))
    print("integer perturbation witnesses verified:", n)
    precision_tests = 0
    for p, h in [(2, 3), (2, 4), (2, 5), (3, 2), (3, 3), (5, 2), (7, 2)]:
        t = p ** h
        a = h if p > 2 else h - 1
        N = t - 1 + p ** (a - 1)
        # Subtract the Taylor polynomial through order t-2 at X=1.
        poly = {N: 1}
        for j in range(t - 1):
            poly[j] = -sum(comb(N, k) * comb(k, j) * (-1) ** (k-j)
                           for k in range(j, t - 1))
        assert open_roots(poly, p)[0] >= t
        assert valuation(comb(N, t-1), p) == h-a+1
        assert valuation(comb(N, t), p) == 0
        precision_tests += 1
    print("direct Newton checks of sharp precision examples:", precision_tests)
    count = 0
    for p, t, r, cap in [(2, 3, Fraction(5,4), 7), (3, 4, Fraction(3,5), 8),
                         (5, 4, Fraction(1,3), 8), (2, 5, Fraction(9,8), 7)]:
        for E in combinations(range(cap), t):
            if E[0] != 0:
                continue
            analytic = closed_by_minors(E, p, r, True)
            direct = closed_by_minors(E, p, r, False)
            assert analytic == direct, (p, E, r, analytic, direct)
            count += 1
    print("independent binomial/exponential minimum-minor comparisons:", count)


if __name__ == "__main__":
    main()
