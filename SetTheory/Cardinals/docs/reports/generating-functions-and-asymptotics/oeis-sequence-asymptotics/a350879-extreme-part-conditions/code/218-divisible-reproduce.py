#!/usr/bin/env python3
"""Exact, standard-library reproduction for the A117086 deficit report.

All arithmetic used in mathematical checks is integer or Fraction arithmetic.
No saved data, computer algebra system, numerical constants, network, or private
research files are inputs. See README.md for algorithms and certificate scope.
"""
from __future__ import annotations

import argparse
import csv
from fractions import Fraction as F
import hashlib
import io
import json
from math import factorial
from pathlib import Path

from uniform_certificates import endpoint_certificates


def require(condition, message):
    """A runtime check, deliberately not an assertion (also active under -O)."""
    if not condition:
        raise RuntimeError(message)


def integer(value, name, minimum=0):
    if type(value) is not int:
        raise TypeError(f"{name} must be an integer, excluding bool")
    if value < minimum:
        raise ValueError(f"{name} must be at least {minimum}")
    return value


def rational(value, name):
    if type(value) not in (int, F):
        raise TypeError(f"{name} must be an int or Fraction, excluding bool")
    return F(value)


def partition_numbers(N):
    """Euler's pentagonal recurrence, for p(0),...,p(N)."""
    integer(N, "N")
    p = [1] + [0] * N
    for n in range(1, N + 1):
        k = 1
        while k * (3 * k - 1) // 2 <= n:
            j = k * (3 * k - 1) // 2
            sign = 1 if k % 2 else -1
            p[n] += sign * p[n - j]
            j = k * (3 * k + 1) // 2
            if j <= n:
                p[n] += sign * p[n - j]
            k += 1
    return p


def partition_numbers_knapsack(N):
    """Independent unrestricted-part product dynamic program."""
    integer(N, "N")
    p = [1] + [0] * N
    for part in range(1, N + 1):
        for n in range(part, N + 1):
            p[n] += p[n - part]
    return p


def divisible_counts(N):
    """Count by original minimum k and maximum M; a(0)=0.

    Remove one k and one M, leaving parts in [k,M]. When M=k this
    counts multiplicity at least two; the initial ones count singletons.
    The shrinking residual bound is safe: future bounds only decrease.
    """
    integer(N, "N")
    a = [0] + [1] * N
    for k in range(1, N // 2 + 1):
        dp = [1] + [0] * (N - k)
        for M in range(k, N - k + 1):
            bound = N - k - M
            for s in range(M, bound + 1):
                dp[s] += dp[s - M]
            if M % k == 0:
                for s in range(bound + 1):
                    a[k + M + s] += dp[s]
    return a


def conjugate_counts(N):
    """Independent DP: length divisible by multiplicity of the maximum.

    For conjugate mu, the original smallest part is the multiplicity j
    of max(mu), and the original largest part is length(mu). Before
    introducing M, dp[s][ell] counts partitions using only parts <M.
    Adding j copies of M is admissible exactly when j divides ell.
    This algorithm never classifies original minima or maxima.
    """
    integer(N, "N")
    dp = [[0] * (n + 1) for n in range(N + 1)]
    dp[0][0] = 1
    a = [0] * (N + 1)
    for M in range(1, N + 1):
        for j in range(1, N // M + 1):
            shift = j * M
            for s in range(N - shift + 1):
                a[shift + s] += sum(dp[s][ell] for ell in range(0, s + 1, j))
        for s in range(M, N + 1):
            for ell in range(1, s - M + 2):
                dp[s][ell] += dp[s - M][ell - 1]
    return a, [sum(row) for row in dp]


def enumerate_partitions(n, maximum=None):
    """Generate nonincreasing tuples, independent of both counting DPs."""
    integer(n, "n")
    if maximum is None:
        maximum = n
    integer(maximum, "maximum")
    if n == 0:
        yield ()
    else:
        for part in range(min(n, maximum), 0, -1):
            for rest in enumerate_partitions(n - part, part):
                yield (part,) + rest


# Small exact polynomial/series primitives: coefficient lists in ascending order.
def _mul(a, b, degree=None):
    degree = len(a) + len(b) - 2 if degree is None else degree
    out = [F(0)] * (degree + 1)
    for i, x in enumerate(a[:degree + 1]):
        if x:
            for j, y in enumerate(b[:degree - i + 1]):
                if y:
                    out[i + j] += x * y
    return out


def _q_product(K):
    out = [1]
    for j in range(1, K + 1):
        # Direct multiplication by 1-q^j, with integer coefficients.
        nxt = out + [0] * j
        for d, v in enumerate(out):
            nxt[d + j] -= v
        out = nxt
    return out


def radial_coefficients(L):
    """g_0,...,g_L from telescoped exponential-series products."""
    integer(L, "L")
    g = [F(0)] * (L + 1)
    product = [F(1)] + [F(0)] * L
    for k in range(1, L + 1):
        factor = [F(0)] + [F((-1) ** (j + 1) * k ** j, factorial(j))
                            for j in range(1, L + 1)]
        product = _mul(product, factor, L)
        for j in range(L + 1):
            g[j] += product[j] / (k * (k + 1))
    return g


def radial_moments(L):
    """Independent route: finite original-weight polynomial, then moments.

    H(q)=sum_{k=2}^{L+1}(k-1)/k q^k product_{j<k}(1-q^j).
    Its coefficient moments give [z^ell]H(exp(-z)); terms omitted from
    the infinite minimum sum have valuation greater than L.
    """
    integer(L, "L")
    h = [F(0)] * ((L + 1) * (L + 2) // 2 + 1)
    for k in range(2, L + 2):
        for j, v in enumerate(_q_product(k - 1)):
            h[j + k] += F(k - 1, k) * v
    return [sum(v * F((-j) ** ell, factorial(ell)) for j, v in enumerate(h))
            for ell in range(L + 1)]


def derivative_polynomials(L):
    """Q_ell(x), x=t/A, by differentiation recurrence, checked factorially."""
    integer(L, "L")
    Q = [[F(1), F(-1, 2)]]
    for ell in range(L):
        q = Q[-1]
        nxt = q + [F(0)]
        for j, v in enumerate(q):
            nxt[j + 1] -= F(ell + 2 + j, 2) * v
        Q.append(nxt)
    for ell, q in enumerate(Q):
        closed = [F((-1) ** h * factorial(ell + h + 1),
                    factorial(ell + 1 - h) * factorial(h) * 4 ** h)
                  for h in range(ell + 2)]
        require(q == closed, f"derivative recurrence/factorial mismatch at {ell}")
    return Q


def correction_coefficients(R):
    """c_m in Q[A^-1], as dict {nonnegative exponent: rational coefficient}."""
    integer(R, "R")
    g, Q = radial_coefficients(R + 1), derivative_polynomials(R + 1)
    out = []
    for m in range(R + 1):
        c = {}
        for ell in range(1, m + 2):
            h = m + 1 - ell
            if h < len(Q[ell]):
                v = 2 * g[ell] * Q[ell][h]
                if v:
                    c[h] = c.get(h, F(0)) + v
        out.append(c)
    return out


def fixed_minimum_residues(N, k, m):
    """Original maximum-residue counts, by bounded-part knapsack."""
    integer(N, "N"); integer(k, "k", 1); integer(m, "m", 2)
    out = [[0] * m for _ in range(N + 1)]
    for n in range(k, N + 1, k):
        out[n][k % m] += 1
    dp = [1] + [0] * N
    for M in range(k, N + 1):
        for s in range(M, N + 1):
            dp[s] += dp[s - M]
        if M > k:
            for n in range(k + M, N + 1):
                out[n][M % m] += dp[n - k - M]
    return out


def _length_residues(N, m):
    dp = [[0] * m for _ in range(N + 1)]
    dp[0][0] = 1
    for part in range(1, N + 1):
        for n in range(part, N + 1):
            for b in range(m):
                dp[n][(b + 1) % m] += dp[n - part][b]
    return dp


def fourier_reduction(N, k, m):
    """Exact reduction in Z[q,z]/(q^(N+1),z^m-1), including correction R_k."""
    integer(N, "N"); integer(k, "k", 1); integer(m, "m", 2)
    dp = _length_residues(N, m)
    out = [[0] * m for _ in range(N + 1)]
    for d, h in enumerate(_q_product(k - 1)):
        for n in range(k + d, N + 1):
            for b in range(m):
                out[n][b] += h * dp[n - k - d][b]
    if k <= N:
        out[k][k % m] += 1
    for M in range(k):
        h = [1]
        for j in range(M + 1, k):
            nxt = h + [0] * j
            for d, v in enumerate(h):
                nxt[d + j] -= v
            h = nxt
        for d, v in enumerate(h):
            if k + M + d <= N:
                out[k + M + d][M % m] -= v
    return out


# Rational formal inversion; no Lambert W or floating-point evaluation is used.
def _series_inverse(a, M):
    require(a[0] == 1, "formal reciprocal requires constant coefficient one")
    b = [F(1)] + [F(0)] * M
    for n in range(1, M + 1):
        b[n] = -sum(a[k] * b[n - k] for k in range(1, min(n, len(a) - 1) + 1))
    return b


def _series_log(a, M):
    require(a[0] == 1, "formal logarithm requires constant coefficient one")
    inv = _series_inverse(a, M)
    derivative = [j * a[j] for j in range(1, len(a))]
    product = _mul(derivative, inv, max(0, M - 1))
    return [F(0)] + [product[j - 1] / j for j in range(1, M + 1)]


def _series_exp(a, M):
    require(a[0] == 0, "formal exponential requires zero constant coefficient")
    b = [F(1)] + [F(0)] * M
    for n in range(1, M + 1):
        b[n] = sum(k * a[k] * b[n - k] for k in range(1, n + 1)) / n
    return b


def _compose_d(d, z, M):
    out = [F(1)] + [F(0)] * M
    power = [F(1)] + [F(0)] * M
    for j in range(1, M + 1):
        power = _mul(power, z, M)
        for k, v in enumerate(power):
            out[k] += d[j] * v
    return out


def _log_residual(delta, beta, d, M):
    h = [F(1)] + delta[:M]  # 1+u Delta
    inv = _series_inverse(h, M)
    z = [F(0)] + inv[:M]    # u/(1+u Delta)
    logh = _series_log(h, M)
    logd = _series_log(_compose_d(d, z, M), M)
    return [delta[j] - beta * logh[j] + logd[j] for j in range(M + 1)]


def inverse_coefficients(beta, d, M):
    """Triangular coefficients v_1,...,v_M for exact rational d_j.

    Input d is [1,d_1,...,d_M]; beta is a positive integer. Each step
    checks its unit coefficient and cancellation. A separate multiplicative
    residual, using exp rather than log, checks the final answer.
    """
    integer(beta, "beta", 1); integer(M, "M", 1)
    if not isinstance(d, (list, tuple)) or len(d) < M + 1:
        raise ValueError("d must contain a constant and at least M coefficients")
    d = [rational(v, "d coefficient") for v in d[:M + 1]]
    if d[0] != 1:
        raise ValueError("d[0] must be one")
    delta = [F(0)] * (M + 1)
    for m in range(1, M + 1):
        base = _log_residual(delta[:m + 1], beta, d, m)[m]
        trial = delta[:m + 1]
        trial[m] = F(1)
        require(_log_residual(trial, beta, d, m)[m] - base == 1,
                f"inverse is not triangular at order {m}")
        delta[m] = -base
        require(all(v == 0 for v in _log_residual(delta[:m + 1], beta, d, m)),
                f"logarithmic inverse residual at order {m}")
    h = [F(1)] + delta[:M]
    inv = _series_inverse(h, M)
    hpower = [F(1)] + [F(0)] * M
    for _ in range(beta):
        hpower = _mul(hpower, inv, M)
    z = [F(0)] + inv[:M]
    residual = _mul(_mul(_series_exp(delta, M), hpower, M), _compose_d(d, z, M), M)
    require(residual == [F(1)] + [F(0)] * M, "multiplicative inverse residual")
    d1, d2, d3 = d[1:4] if M >= 3 else (F(0), F(0), F(0))
    if M >= 3:
        expected = [-d1, -beta * d1 + d1 * d1 / 2 - d2,
                    -beta ** 2 * d1 + (F(beta, 2) - 1) * d1 * d1 - beta * d2
                    - d1 ** 3 / 3 + d1 * d2 - d3]
        require(delta[1:4] == expected, "displayed inverse coefficients")
    return delta[1:]


def _ceil(x):
    return -(-x.numerator // x.denominator)


def partition_product_upper(r, places=100):
    """Certified rational upper bound for P(r), with log-tail certificate.

    Every finite factor multiplication is rounded upward on a decimal grid.
    For omitted j>J, log product <= delta = r^(J+1)/((1-r)(1-r^(J+1))).
    Once delta<10^-30, exp(delta)<=1/(1-delta) closes the certificate.
    """
    r = rational(r, "r"); integer(places, "places", 1)
    if not 0 < r < 1:
        raise ValueError("r must satisfy 0<r<1")
    scale, power, J = 10 ** places, F(1), 0
    value = scale
    while True:
        J += 1
        power *= r
        value = _ceil(F(value) / (1 - power))
        nextpower = power * r
        delta = nextpower / ((1 - r) * (1 - nextpower))
        if delta < F(1, 10 ** 30):
            break
    require(0 < delta < 1, "invalid product tail")
    value = _ceil(F(value) / (1 - delta))
    return F(value, scale), J, delta


def exp_negative_upper(x, terms=140):
    """e^-x <= 1/sum_{j=0}^terms x^j/j! for x>=0, all rational."""
    x = rational(x, "x"); integer(terms, "terms", 1)
    if x < 0:
        raise ValueError("x must be nonnegative")
    term, total = F(1), F(1)
    for k in range(1, terms + 1):
        term *= x / k
        total += term
    return 1 / total


def finite_enclosure(n, K, r, p):
    """Certified (4.4), for K in {2,3,4}, whose cosine gaps are rational.

    p must be an exact partition table through n. It is checked against an
    independently regenerated Euler table, rather than trusted as input.
    """
    integer(n, "n", 1); integer(K, "K", 2)
    if K > 4:
        raise ValueError("this rational-cosine implementation supports only K=2,3,4")
    if n <= K * (K + 1) // 2:
        raise ValueError("n must exceed K(K+1)/2 for the polynomial correction to vanish")
    r = rational(r, "r")
    if not 0 < r < 1:
        raise ValueError("r must satisfy 0<r<1")
    if not isinstance(p, (list, tuple)) or len(p) <= n:
        raise ValueError("p must contain entries p(0),...,p(n)")
    for v in p[:n + 1]:
        integer(v, "partition table entry")
    if list(p[:n + 1]) != partition_numbers(n):
        raise ValueError("p is not the exact partition table")
    gaps = {2: [F(2)], 3: [F(3, 2), F(3, 2)], 4: [F(1), F(2), F(1)]}
    Pupper, J, delta = partition_product_upper(r)
    sigma = F(0)
    for k in range(2, K + 1):
        pref = r ** k / k
        for j in range(1, k):
            pref *= 1 + r ** j
        sigma += pref * sum(exp_negative_upper(r * r * gap / (1 - r * r))
                            for gap in gaps[k])
    error = _ceil(r ** (-n) * Pupper * sigma)
    s = F(0)
    for k in range(2, K + 1):
        s += F(k - 1, k) * sum(v * p[n - k - j]
                              for j, v in enumerate(_q_product(k - 1)) if n >= k + j)
    u = sum(v * p[n - j] for j, v in enumerate(_q_product(K)) if n >= j)
    upper = s + u + error
    return {"n": n, "K": K, "r": str(r), "product_factors": J,
            "product_rounding_decimal_places": 100, "product_tail_target": "1/1000000000000000000000000000000",
            "exponential_terms": 140, "product_upper": str(Pupper), "product_log_tail_upper": str(delta),
            "s_exact": str(s), "u_exact": str(u), "E_upper_integer": str(error),
            "lower_integer": str(_ceil(s - error)),
            "upper_integer": str(upper.numerator // upper.denominator)}


def _tex_fraction(x):
    x = F(x)
    return str(x.numerator) if x.denominator == 1 else rf"\frac{{{x.numerator}}}{{{x.denominator}}}"


def _tex_polynomial(c):
    terms = []
    for h, v in sorted(c.items()):
        if v:
            sign = "-" if v < 0 else "+"
            v = abs(v)
            numerator = str(v.numerator)
            denominator = "" if v.denominator == 1 else str(v.denominator)
            if h:
                denominator += "A" if h == 1 else rf"A^{{{h}}}"
            term = numerator if not denominator else rf"\frac{{{numerator}}}{{{denominator}}}"
            terms.append((sign if terms or sign == "-" else "") + term)
    return "".join(terms) or "0"


def _tabular(headers, rows, alignment):
    return ("% Generated by code/reproduce.py; do not edit.\n"
            + rf"\begin{{tabular}}{{{alignment}}}" + "\n\\hline\n"
            + " & ".join(headers) + " \\\\\n\\hline\n"
            + "".join(" & ".join(row) + " \\\\\n" for row in rows)
            + "\\hline\n\\end{tabular}\n")


def _validation_checks():
    """Exercise type/domain checks, including bool exclusion and runtime guards."""
    bad = [(partition_numbers, (True,)), (partition_numbers, (-1,)),
           (divisible_counts, (1.0,)), (conjugate_counts, (False,)),
           (radial_coefficients, (F(2),)), (radial_moments, (-1,)),
           (derivative_polynomials, (True,)), (correction_coefficients, (-1,)),
           (fixed_minimum_residues, (10, 0, 2)), (fourier_reduction, (10, 1, 1)),
           (fourier_reduction, (10, True, 2)), (partition_product_upper, (0,)),
           (partition_product_upper, (F(1),)), (partition_product_upper, (0.5,)),
           (exp_negative_upper, (-1,)), (exp_negative_upper, (1, True)),
           (inverse_coefficients, (True, [1, 1], 1)),
           (inverse_coefficients, (2, [1, True], 1)),
           (inverse_coefficients, (2, [0, 1], 1)),
           (finite_enclosure, (100, 5, F(1, 2), [1] * 101)),
           (finite_enclosure, (6, 3, F(1, 2), [1] * 7)),
           (finite_enclosure, (10, 2, F(1, 2), [1] * 11))]
    for function, args in bad:
        try:
            function(*args)
        except (TypeError, ValueError):
            pass
        else:
            raise RuntimeError(f"input validation accepted {function.__name__}{args!r}")
    try:
        require(False, "guard probe")
    except RuntimeError as exc:
        require(str(exc) == "guard probe", "guard test failure")
    else:
        raise RuntimeError("runtime guards were disabled")
    return len(bad)


def reproduce(N, output):
    """Regenerate all checks, semantic JSON, CSV, and article TeX tables."""
    integer(N, "N", 1000)
    output = Path(output)
    output.mkdir(parents=True, exist_ok=True)
    validations = _validation_checks()
    uniform = endpoint_certificates()
    p, a = partition_numbers(N), divisible_counts(N)
    require(p == partition_numbers_knapsack(N), "independent partition table mismatch")
    D = [0] + [p[n] - a[n] for n in range(1, N + 1)]
    for n in range(1, N + 1):
        require(p[n - 1] <= a[n] <= p[n], f"sandwich failure at n={n}")
    ca, cp = conjugate_counts(220)
    require(ca == a[:221], "independent conjugate count mismatch")
    require(cp == p[:221], "conjugate DP unrestricted totals mismatch")
    for n in range(1, 36):
        values = list(enumerate_partitions(n))
        require(len(values) == p[n], f"enumeration partition count at {n}")
        require(sum(lam[0] % lam[-1] == 0 for lam in values) == a[n],
                f"enumeration divisible count at {n}")
    for k in range(1, 8):
        for m in range(2, 9):
            require(fixed_minimum_residues(70, k, m) == fourier_reduction(70, k, m),
                    f"group-ring Fourier reduction mismatch k={k}, m={m}")
    g = radial_coefficients(20)
    require(g == radial_moments(20), "independent radial coefficient mismatch")
    Q = derivative_polynomials(20)
    c = correction_coefficients(12)
    # Check the transfer generator against the factorial sum using moment g.
    gm = radial_moments(13)
    for m in range(13):
        oracle = {}
        for ell in range(1, m + 2):
            h = m + 1 - ell
            if h <= ell + 1:
                oracle[h] = 2 * gm[ell] * F((-1) ** h * factorial(ell + h + 1),
                                             factorial(ell + 1 - h) * factorial(h) * 4 ** h)
        require(c[m] == {h: v for h, v in oracle.items() if v}, f"c oracle at {m}")
    substitutions = [F(1, 5), F(1, 3), F(1, 2), F(2, 3), F(3, 4), F(1), F(5, 4),
                     F(3, 2), F(8, 5), F(5, 3), F(2), F(7, 3), F(3), F(10, 3),
                     F(4), F(5), F(6), F(7), F(8), F(10)]
    inverse_results = []
    for A in substitutions:
        dD = [sum(v * A ** (-h) for h, v in cm.items()) * (2 * A) ** j
              for j, cm in enumerate(c)]
        da = [F(1), -(A + 1)] + [-A * dD[j - 1] for j in range(2, 13)]
        for label, beta, d in [("D", 3, dD), ("a", 2, da)]:
            v = inverse_coefficients(beta, d, 12)
            inverse_results.append({"statistic": label, "A": str(A),
                                    "v_1_to_12": [str(x) for x in v],
                                    "log_residual_zero_through": 12,
                                    "multiplicative_residual_zero_through": 12})
    # All breakpoints and immediately following half-integers in a finite range.
    tests = set()
    for n in range(1, 220):
        for value in (p[n], a[n]):
            if value > 1:
                tests.update((F(value), F(value) + F(1, 2)))
    threshold_checks = 0
    for y in sorted(tests):
        ip = next(n for n in range(N + 1) if p[n] >= y)
        ia = next(n for n in range(1, N + 1) if a[n] >= y)
        require(ip <= ia <= ip + 1, "exact inverse shortcut failed")
        threshold_checks += 1
    enclosure = finite_enclosure(1000, 3, F(24, 25), p)
    require(int(enclosure["lower_integer"]) <= D[1000] <= int(enclosure["upper_integer"]),
            "finite enclosure misses regenerated exact count")
    # Published-value regressions check results; none is used to generate them.
    require(enclosure["lower_integer"] == "472725439956575758375747068463", "lower bound changed")
    require(enclosure["upper_integer"] == "481748117158362419220289068699", "upper bound changed")
    require(D[1000] == 479221051806021018167049012329, "exact deficit changed")
    require(enclosure["product_factors"] == 1771, "product cutoff changed")
    enclosure["exact_deficit"] = str(D[1000])
    # Certified inverse shortcut at m=nu_p(y), including both rational
    # endpoints. The lower test is inclusive; the upper test must be strict.
    s, u, error = (F(enclosure[key]) for key in ("s_exact", "u_exact", "E_upper_integer"))
    a_lower, a_upper = p[1000] - s - u - error, p[1000] - s + error
    require(a_lower <= a[1000] <= a_upper, "complemented a enclosure")
    shortcut_tests = []
    for y in (a_lower - F(1, 2), a_lower, a_lower + F(1, 2),
              a_upper - F(1, 2), a_upper, a_upper + F(1, 2),
              F(a[1000]), F(a[1000]) + F(1, 2)):
        require(p[999] < y <= p[1000], "shortcut test does not have nu_p(y)=1000")
        if a_lower >= y:
            answer, route = 1000, "lower_bound"
        elif a_upper < y:
            answer, route = 1001, "upper_bound"
        else:
            answer, route = (1000 if a[1000] >= y else 1001), "exact_fallback"
        require((answer == 1000) == (a[1000] >= y), "certified inverse decision")
        shortcut_tests.append({"y": str(y), "nu_p": 1000, "nu_a": answer, "route": route})
    require(shortcut_tests[1]["route"] == "lower_bound", "lower endpoint inclusivity")
    require(shortcut_tests[4]["route"] == "exact_fallback", "upper endpoint strictness")
    require(shortcut_tests[5]["route"] == "upper_bound", "upper bound branch")
    counts = [{"n": n, "p": str(p[n]), "a": str(a[n]), "D": str(D[n])}
              for n in (10, 20, 50, 100, 200, 500, 1000)]
    if N != 1000:
        counts.append({"n": N, "p": str(p[N]), "a": str(a[N]), "D": str(D[N])})
    stream = io.StringIO(newline="")
    writer = csv.writer(stream, lineterminator="\n")
    writer.writerow(("n", "p", "a117086", "deficit"))
    writer.writerows((n, p[n], a[n], D[n]) for n in range(N + 1))
    csv_text = stream.getvalue()
    (output / "exact_values.csv").write_text(csv_text, encoding="utf-8", newline="\n")
    receipt = {"schema": "A117086-deficit-reproduction-v2", "status": "passed", "N": N,
               "conventions": {"p(0)": 1, "a(0)": 0, "D(0)": "0 by bookkeeping convention; D(n)=p(n)-a(n) only for n>=1"},
               "checks": {"partition_euler_vs_knapsack_through": N, "original_min_max_counts_through": N,
                          "independent_conjugate_counts_through": 220, "brute_enumeration_through": 35,
                          "exact_sandwich_indices": N, "fourier_group_ring_cases": 49,
                          "fourier_indices": [0, 70], "radial_product_vs_moments_through": 20,
                          "Q_recurrence_vs_factorial_through": 20, "c_independent_generators_through": 12,
                          "inverse_specialization_cases": len(inverse_results), "inverse_residual_order": 12,
                          "exact_threshold_breakpoint_tests": threshold_checks, "invalid_input_tests": validations,
                          "certified_inverse_shortcut_endpoint_tests": len(shortcut_tests),
                          "uniform_error_endpoint_certificates": uniform["endpoint_count"],
                          "uniform_error_invalid_input_tests": uniform["invalid_input_tests"],
                          "runtime_guard_probe": "passed"},
               "g_0_to_20": [str(v) for v in g],
               "Q_0_to_20_coefficients_in_t_over_A": [[str(v) for v in q] for q in Q],
               "c_0_to_12_polynomials_in_A_inverse": [{str(h): str(v) for h, v in sorted(cm.items())} for cm in c],
               "inverse_specializations": inverse_results, "certified_finite_enclosure": enclosure,
               "certified_inverse_shortcut_tests": shortcut_tests,
               "uniform_reciprocal_minimum_certificates": uniform,
               "selected_exact_counts": counts,
               "exact_values_csv_sha256": hashlib.sha256(csv_text.encode("utf-8")).hexdigest()}
    (output / "receipt.json").write_text(json.dumps(receipt, indent=2, sort_keys=True) + "\n", encoding="utf-8", newline="\n")
    tables = {
        "radial_coefficients.tex": _tabular([r"$\ell$", r"$g_\ell$", r"$\ell$", r"$g_\ell$"],
            [[str(j), "$" + _tex_fraction(g[j]) + "$", str(j + 6), "$" + _tex_fraction(g[j + 6]) + "$"]
             for j in range(1, 7)], "r l r l"),
        "forward_coefficients.tex": _tabular(["$m$", "$c_m$"],
            [[str(m), "$" + _tex_polynomial(c[m]) + "$"] for m in range(6)], "r l"),
        "exact_counts.tex": _tabular(["$n$", "$p(n)$", "$a(n)$", "$D(n)$"],
            [[str(row["n"]), row["p"], row["a"], row["D"]] for row in counts if row["n"] <= 200],
            "r r r r") + "\n\\par\\medskip\n\n" + _tabular(["Quantity", "Exact value"],
            [[f"${name}({row['n']})$", row[name]]
             for row in counts if row["n"] > 200 for name in ("p", "a", "D")], "l r"),
        "finite_enclosure.tex": _tabular(["Quantity", "Exact value"],
            [["Lower bound", enclosure["lower_integer"]], ["$D(1000)$", str(D[1000])],
             ["Upper bound", enclosure["upper_integer"]], ["Product factors", str(enclosure["product_factors"])],
             ["Exponential degree $H$", str(enclosure["exponential_terms"])]], "l r"),
        "verification_summary.tex": _tabular(["Exact check", "Range or count"],
            [["Euler recurrence versus partition knapsack", f"$0\\le n\\le {N}$"],
             ["Original extrema versus conjugate statistic", "$0\\le n\\le220$"],
             ["Direct partition enumeration", "$1\\le n\\le35$"],
             ["Fourier reduction in the integral group ring", "49 cases, $0\\le n\\le70$"],
             ["Radial product versus finite moments", "degree 20"],
             ["Derivative recurrence versus factorial formula", "$Q_0,\\ldots,Q_{20}$"],
             ["Independent forward-coefficient generators", "$c_0,\\ldots,c_{12}$"],
             ["Rational inverse specializations, both statistics", "40 cases, degree 12"],
             ["Exact threshold breakpoint tests", str(threshold_checks)],
             ["Certified inverse endpoint tests", str(len(shortcut_tests))],
             ["Uniform error bound, $n\\ge90$", "19 rational endpoint certificates"],
             ["Uniform certificate invalid-input probes", str(uniform["invalid_input_tests"])],
             ["Rejected invalid-input probes", str(validations)]], "l l")}
    for filename, content in tables.items():
        (output / filename).write_text(content, encoding="utf-8", newline="\n")
    print(json.dumps({"status": "passed", "N": N,
                      "exact_values_csv_sha256": receipt["exact_values_csv_sha256"],
                      "certificate": [enclosure["lower_integer"], enclosure["upper_integer"]]}, sort_keys=True))
    return receipt


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--N", type=int, default=1000,
                        help="maximum original count index, at least 1000 (4000 is substantial)")
    parser.add_argument("--output", type=Path, required=True, help="directory for regenerated receipts and TeX tables")
    args = parser.parse_args()
    if args.N < 1000:
        parser.error("--N must be at least 1000 because the finite certificate uses n=1000")
    reproduce(args.N, args.output)


if __name__ == "__main__":
    main()
