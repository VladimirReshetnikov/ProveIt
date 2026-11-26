"""Check delayed-onset spanning-tree formulas. Python 3.9+, standard library."""
from functools import lru_cache
from math import comb


def valuation(n, p):
    assert n != 0
    order = 0
    while n % p == 0:
        n //= p
        order += 1
    return order


def predicted(p, k, n, m=1):
    s = min(k, n)
    return (2 * (p + 1) * (p**n - p**s) // (p - 1)
            + 2 * s * p**n + m * (p**s - 1) + 2 * s - 2 * n)


def cyclotomic_shell(p, k, h, m=1, distinct_steps=False):
    """Use no anisotropy or weight comparison. Work in Z[Z]/Phi_(p^h)."""
    N = p**h
    block = N // p
    e = N - block

    @lru_cache(None)
    def monomial(t):
        # Coefficients in powers of Z-1, after reducing Z^t modulo Phi.
        if t < e:
            return tuple(comb(t, j) if j <= t else 0 for j in range(e))
        # 1 + Z^block + ... + Z^e = 0.
        power = t - e
        terms = [monomial(power + i * block) for i in range(p - 1)]
        return tuple(-sum(row[j] for row in terms) for j in range(e))

    def local_order(a, b):
        if distinct_steps:
            powers = tuple((1 + i * p**k) * a for i in range(p)) + (p**k * a, b)
            multiplicities = (1,) * len(powers)
        else:
            powers = (a, p**k * a, b)
            multiplicities = (p**m, 1, 1)
        coeff = [2 * sum(multiplicities)] + [0] * (e - 1)
        for t, mult in zip(powers, multiplicities):
            pos = monomial(t % N)
            neg = monomial(-t % N)
            for j in range(e):
                coeff[j] -= mult * (pos[j] + neg[j])
        return min(e * valuation(x, p) + j for j, x in enumerate(coeff) if x)

    # Each representative accounts for an entire unit orbit of size e.
    return (sum(local_order(1, b) for b in range(N))
            + sum(local_order(a, 1) for a in range(0, N, p)))


def direct_tree_count(p, k, n, m=1):
    """Exact Matrix-Tree cofactor, using fraction-free Gaussian elimination."""
    N = p**n
    last = N * N - 1
    lap = [[0] * last for _ in range(last)]
    for x in range(N):
        for y in range(N):
            v = x * N + y
            for dx, dy, mult in ((1, 0, p**m), (p**k, 0, 1), (0, 1, 1)):
                w = ((x + dx) % N) * N + (y + dy) % N
                if v == w:
                    continue
                if v < last:
                    lap[v][v] += mult
                if w < last:
                    lap[w][w] += mult
                if v < last and w < last:
                    lap[v][w] -= mult
                    lap[w][v] -= mult
    previous = 1
    for r in range(last - 1):
        pivot = lap[r][r]
        assert pivot > 0  # Every leading submatrix is positive definite.
        for i in range(r + 1, last):
            for j in range(r + 1, last):
                num = pivot * lap[i][j] - lap[i][r] * lap[r][j]
                lap[i][j], rem = divmod(num, previous)
                assert rem == 0
        previous = pivot
    return lap[-1][-1]


def main():
    for p, k, max_level in ((3, 1, 4), (3, 2, 5), (3, 3, 5), (7, 2, 3)):
        actual = 0
        levels = []
        for n in range(1, max_level + 1):
            actual += cyclotomic_shell(p, k, n) - 2
            assert actual == predicted(p, k, n)
            if p**(2 * n) <= 81:
                assert actual == valuation(direct_tree_count(p, k, n), p)
            levels.append(actual)
        print(f"p={p}, k={k}: {levels}")
        if p >= 7:
            distinct = 0
            for n in range(1, max_level + 1):
                distinct += cyclotomic_shell(p, k, n, distinct_steps=True) - 2
                assert distinct == levels[n - 1]
            print(f"Distinct-step version agrees through level {max_level}.")
    print("All cyclotomic evaluations, small graph cofactors, and formulas agree.")


if __name__ == "__main__":
    main()
