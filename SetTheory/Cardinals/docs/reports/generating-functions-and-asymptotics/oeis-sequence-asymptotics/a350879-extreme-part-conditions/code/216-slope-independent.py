"""Different finite verification paths, not a claim of clean-room authorship.

These checks adapt the research audit's algorithms. The count DP does not use
the sieve. Moments expand q-polynomials, rather than exponential products;
Q is differentiated recursively, rather than built from factorials.
"""
from fractions import Fraction as F
from math import factorial
import extremes as core


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def partition_coin_change(N):
    p = [1] + [0] * N
    for part in range(1, N + 1):
        for n in range(part, N + 1):
            p[n] += p[n - part]
    return p


def direct_counts(N, ks, bs):
    """Unbounded coin change indexed by exact length and current maximum.

While adding the coin M, the increment dp[n-M][ell-1] counts partitions
whose largest part is exactly M, including any number of copies of M.
"""
    result = {(kind, k, b): [0] * (N + 1)
              for kind in ("E", "T") for k in ks for b in bs}
    dp = [[0] * (N + 1) for _ in range(N + 1)]; dp[0][0] = 1
    totals = [1] + [0] * N
    for maximum in range(1, N + 1):
        for n in range(maximum, N + 1):
            for length in range(1, n - maximum + 2):
                increment = dp[n - maximum][length - 1]
                if not increment:
                    continue
                dp[n][length] += increment
                totals[n] += increment
                for k in ks:
                    difference = maximum - k * length
                    if difference in bs:
                        result["E", k, difference][n] += increment
                    for b in bs:
                        if b <= difference:
                            result["T", k, b][n] += increment
    require(totals == partition_coin_change(N), "coin-change totals disagree")
    return result


def finite_sieve_polynomial(kind, k, b, J):
    result = {}
    for j in range(1, J + 1):
        D = ((2 * k + 1) * j * j + (2 * b - 1) * j) // 2
        term = {D: (-1) ** (j - 1)}
        for r in range(j + (kind == "T"), k * j + 1):
            new = term.copy()
            for exponent, coefficient in term.items():
                new[exponent + r] = new.get(exponent + r, 0) - coefficient
            term = {e: c for e, c in new.items() if c}
        for exponent, coefficient in term.items():
            result[exponent] = result.get(exponent, 0) + coefficient
    return {e: c for e, c in result.items() if c}


def radial_moments(kind, k, b, degree):
    J = (degree - (kind == "E")) // (k - 1)
    H = finite_sieve_polynomial(kind, k, b, J)
    return [sum((F(c * (-e) ** ell, factorial(ell)) for e, c in H.items()), F(0))
            for ell in range(degree + 1)]


def q_recurrence(ell):
    q = [F(1), F(-1, 2)]
    for j in range(ell):
        previous = q; q = previous + [F(0)]
        for h in range(1, len(q)):
            q[h] -= F(j + h + 1, 2) * previous[h - 1]
    return q


def forward_moments(kind, k, b, order):
    s = k if kind == "E" else k - 1
    g = radial_moments(kind, k, b, s + order)
    c = [{} for _ in range(order + 1)]
    for ell in range(s, s + order + 1):
        for h, q in enumerate(q_recurrence(ell)):
            if ell + h <= s + order:
                m = ell + h - s
                c[m][-h] = c[m].get(-h, F(0)) + g[ell] * q / factorial(k)
    return [core.Laurent(row) for row in c]


def inverse_residual_via_derivative(c, d, u):
    """Second log implementation: integrate F'/F instead of log powers."""
    R = len(c) - 1
    zero, one = core.ZERO, core.ONE

    def product(p, q):
        out = [zero] * (R + 1)
        for n in range(R + 1):
            for j in range(n + 1):
                out[n] += p[j] * q[n - j]
        return out

    def reciprocal(p):
        out = [one] + [zero] * R
        for n in range(1, R + 1):
            out[n] = -sum((p[j] * out[n - j] for j in range(1, n + 1)), zero)
        return out

    def logarithm(p):
        derivative = [(j + 1) * p[j + 1] for j in range(R)] + [zero]
        quotient = product(derivative, reciprocal(p))
        return [zero] + [quotient[j - 1] / j for j in range(1, R + 1)]

    denominator = ([one, zero] + u[1:R])[:R + 1]
    v = [zero] + [2 * core.A * t for t in reciprocal(denominator)[:R]]
    H = [c[R]] + [zero] * R
    for j in range(R - 1, -1, -1):
        H = product(H, v); H[0] += c[j]
    ld, lh = logarithm(denominator), logarithm(H)
    return [u[j] - d * ld[j] + lh[j] for j in range(R + 1)]
