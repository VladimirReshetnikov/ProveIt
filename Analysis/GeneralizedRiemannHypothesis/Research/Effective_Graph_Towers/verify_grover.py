"""Direct exact checks of the square-grid Grover determinant, Python 3.9+."""
from fractions import Fraction
from itertools import product
from math import gcd

DIRECTIONS = ((1, 0), (0, 1), (-1, 0), (0, -1))


def determinant(matrix):
    # Bareiss elimination with row exchanges. No symmetry/definiteness required.
    a = [row[:] for row in matrix]
    previous = sign = 1
    n = len(a)
    for k in range(n - 1):
        r = next((r for r in range(k, n) if a[r][k]), None)
        if r is None:
            return 0
        if r != k:
            a[k], a[r] = a[r], a[k]
            sign = -sign
        pivot = a[k][k]
        for i in range(k + 1, n):
            for j in range(k + 1, n):
                value = pivot * a[i][j] - a[i][k] * a[k][j]
                a[i][j], rem = divmod(value, previous)
                assert rem == 0
        previous = pivot
    return sign * a[-1][-1]


def arc_det(a, n):
    # Every vertex has four outgoing directed arcs, even on the one-vertex
    # base. An inverse arc has its own direction label independent of endpoints.
    L = 3**n
    N = L * L
    M = [[0] * (4 * N) for _ in range(4 * N)]
    for x, y in product(range(L), repeat=2):
        for i, (dx, dy) in enumerate(DIRECTIONS):
            c = 4 * (x * L + y) + i
            M[c][c] += 2 * a
            target = ((x + dx) % L) * L + (y + dy) % L
            for j in range(4):
                # Twice the transition: +1 except for the reversed arc (-1).
                M[4 * target + j][c] -= 1 - 2 * (j == (i + 2) % 4)
    return Fraction(determinant(M), 2**(4 * N))


def vertex_det(a, n):
    L = 3**n
    N = L * L
    M = [[0] * N for _ in range(N)]
    for x, y in product(range(L), repeat=2):
        i = x * L + y
        M[i][i] += 2 * ((a - 1)**2 + 2 * a)
        for dx, dy in DIRECTIONS:
            j = ((x + dx) % L) * L + (y + dy) % L
            M[i][j] -= a
    return Fraction((a*a - 1)**N * determinant(M), 2**N)


def valuation(n):
    assert n
    i = 0
    while n % 3 == 0:
        n //= 3
        i += 1
    return i


def formula(a, n):
    if a % 3 == 1:
        m = valuation(a - 1)
        return m * 9**n + 4 * 3**n + 2 * m - 4
    if a % 3 == 2:
        return valuation(a + 1) * 9**n
    return 0


def periodic_kernel(L, M):
    """Compute ker(U^(2g)-I) directly on directed arcs using integers."""
    D = 4 * L * M
    g = gcd(L, M)
    steps = []
    for x in range(L):
        for y in range(M):
            for i, (dx, dy) in enumerate(DIRECTIONS):
                target = ((x + dx) % L) * M + (y + dy) % M
                steps.append([(4 * target + j, 1 - 2 * (j == (i + 2) % 4))
                              for j in range(4)])
    rows = []
    for source in range(D):
        col = [int(i == source) for i in range(D)]
        for _ in range(2 * g):
            out = [0] * D
            for value, edges in zip(col, steps):
                for target, sign in edges:
                    out[target] += sign * value
            col = out
        col[source] -= 2**(2*g)
        rows.append(list(map(Fraction, col)))
    # Rank of the transpose yields the same nullity.
    rank = 0
    for c in range(D):
        r = next((i for i in range(rank, D) if rows[i][c]), None)
        if r is None:
            continue
        rows[rank], rows[r] = rows[r], rows[rank]
        for j in range(rank + 1, D):
            if rows[j][c]:
                q = rows[j][c] / rows[rank][c]
                rows[j] = [x - q*y for x,y in zip(rows[j], rows[rank])]
        rank += 1
    return D - rank


def main():
    for a in (-2, 0, 4, 5, 8, 10):
        values = []
        for n in range(3):
            v = vertex_det(a, n)
            if n <= 1:
                assert v == arc_det(a, n)
            value = valuation(v.numerator) - valuation(v.denominator)
            assert value == formula(a, n)
            values.append(value)
        print(f"a={a:2d}: {values}")
    print("Exact arc determinants agree with the vertex factorization at n=0,1.")
    print("Exact vertex determinants agree with all three valuation formulas at n=0,1,2.")
    for L, M in ((1, 1), (3, 3), (3, 5), (5, 5)):
        dim = periodic_kernel(L, M)
        assert dim == 2 * L * M + 4 * gcd(L, M) - 2
        print(f"{L}x{M}: periodic kernel dimension {dim}")


if __name__ == "__main__":
    main()
