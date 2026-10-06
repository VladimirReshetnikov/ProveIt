"""Independent exact finite counts; all returned values are Python integers."""
from fractions import Fraction
from math import comb, factorial

KNOWN = [1,1,4,26,260,3368,53744,1022320,22522960,565532992,
         15915225216,496911749920,17029582652416,636101065346560,
         25705530908501760,1118038500044633088,52054862490790200576,
         2584158975023147147264]


def require_n(n):
    if isinstance(n, bool) or not isinstance(n, int) or n < 0:
        raise ValueError('board size must be a nonnegative integer')


def stirling_table(max_n):
    require_n(max_n)
    table = [[1]]
    for n in range(1, max_n+1):
        old = table[-1]
        table.append([0]+[old[k-1]+(k*old[k] if k < len(old) else 0)
                          for k in range(1, n+1)])
    return table


def stirling_count(n, table):
    """Direct two-color binomial-Stirling convolution (no Santos recurrence)."""
    require_n(n)
    if len(table) <= n:
        raise ValueError('Stirling table is too short')
    if n == 0:
        return 1
    h, g = (n+1)//2, n//2
    factors = []
    for m in (h, g):
        co = [0]*(n+1)
        for a in range(m+1):
            weight = comb(m, a)
            for k, value in enumerate(table[n-a]):
                co[k] += weight*value
        factors.append(co)
    return sum(factors[0][k]*factors[1][n-k] for k in range(n+1))


def santos_counts(max_n):
    """Ferrers row recurrences; output B_0,...,B_max_n."""
    require_n(max_n)
    W = K = [1]
    result = [1]
    for n in range(1, max_n+1):
        oldW, oldK = W, K
        W, K = oldW+[0], oldK+[0]
        for j in range(1, n+1):
            W[j] += (n-j+n%2)*oldW[j-1]
            K[j] += (n-j+1-n%2)*oldK[j-1]
        result.append(sum(W[j]*K[n-j] for j in range(n+1)))
    return result


def board_color_ie(n, color):
    """Rook inclusion-exclusion built from actual board diagonal incidence."""
    require_n(n)
    if color not in (0, 1):
        raise ValueError('color must be 0 or 1')
    left = sorted({i-j for i in range(n) for j in range(n) if (i+j)%2 == color})
    right = sorted({i+j for i in range(n) for j in range(n) if (i+j)%2 == color})
    bits = {a: 1 << k for k, a in enumerate(right)}
    masks = [sum(bits[i+j] for i in range(n) for j in range(n)
                 if i-j == a and (i+j)%2 == color) for a in left]
    m = len(right)
    out = [0]*(n+1)
    for subset in range(1 << m):
        size = subset.bit_count()
        e = [1]+[0]*len(left)
        for mask in masks:
            degree = (subset & mask).bit_count()
            for k in range(len(left), 0, -1):
                e[k] += degree*e[k-1]
        for k in range(size, min(len(left), m)+1):
            out[k] += (-1)**(k-size)*comb(m-size, k-size)*e[k]
    return out


def board_counts(n):
    """All k-bishop counts, 0<=k<=n, via the actual board incidence graph."""
    a, b = board_color_ie(n, 0), board_color_ie(n, 1)
    return [sum(a[j]*b[k-j] for j in range(k+1)) for k in range(n+1)]


def literal_counts(n):
    """Literal increasing cell-subset search, no color factorization or recurrence.

    Exponential, intentionally limited by the CLI to n<=6 (default 5).
    """
    require_n(n)
    out = [0]*(n+1)
    def search(start, k, descending, ascending):
        out[k] += 1
        if k == n:
            return
        for cell in range(start, n*n):
            i, j = divmod(cell, n)
            a, b = 1 << (i-j+n-1), 1 << (i+j)
            if not (descending & a or ascending & b):
                search(cell+1, k+1, descending | a, ascending | b)
    search(0, 0, 0, 0)
    return out


def coefficient_count(n):
    """Direct rational bivariate extraction n! [x^n y^n] F^n H_h H_g."""
    require_n(n)
    if n == 0:
        return 1
    f = {}
    for k in range(1, n+1):
        f[k, 0] = f[0, k] = Fraction(1, factorial(k))
    power = {(0, 0): Fraction(1)}
    for _ in range(n):
        nxt = {}
        for (a, b), value in power.items():
            for (c, e), weight in f.items():
                if a+c <= n and b+e <= n:
                    key = (a+c, b+e)
                    nxt[key] = nxt.get(key, Fraction(0))+value*weight
        power = nxt
    h, g = (n+1)//2, n//2
    def H(k, a):
        return Fraction(comb(k, a)*factorial(n-a), factorial(n))
    coefficient = factorial(n)*sum((power.get((n-a, n-b), Fraction(0))*H(h, a)*H(g, b)
                                    for a in range(h+1) for b in range(g+1)), Fraction(0))
    if coefficient.denominator != 1:
        raise ArithmeticError('coefficient extraction was not integral')
    return coefficient.numerator
