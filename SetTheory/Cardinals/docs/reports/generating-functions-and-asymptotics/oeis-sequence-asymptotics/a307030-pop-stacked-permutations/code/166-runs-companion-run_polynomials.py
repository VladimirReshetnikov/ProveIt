"""Exact, bounded run-refined pop-stacked permutation computations.

Only Python's standard library is used. Importing this module does not compute a
triangle. All public computations return in-memory data; no file or network API
is used. Coefficient lists are in ascending powers of u and omit trailing zeros.
"""

from fractions import Fraction
from itertools import permutations
from math import comb, factorial

MAX_N = 40
MAX_LITERAL_N = 9
MAX_FILTRATION_K = 12


class CheckFailure(RuntimeError):
    """A mathematical or implementation check did not hold."""


def require(condition, message):
    """An explicit check, deliberately unaffected by python -O."""
    if not condition:
        raise CheckFailure(message)


def bounded_integer(value, name, lower, upper):
    """Validate bounded work requests, rejecting bool as an integer argument."""
    if type(value) is not int or not lower <= value <= upper:
        raise ValueError(f"{name} must be an integer in [{lower}, {upper}]")
    return value


def _trim(a):
    while len(a) > 1 and not a[-1]:
        a.pop()
    return a


def _poly_add(a, b):
    result = [Fraction(0)] * max(len(a), len(b))
    for i, value in enumerate(a):
        result[i] += value
    for i, value in enumerate(b):
        result[i] += value
    return _trim(result)


def _poly_scale(a, value):
    return _trim([value * coefficient for coefficient in a])


def _poly_multiply(a, b):
    result = [Fraction(0)] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        if x:
            for j, y in enumerate(b):
                if y:
                    result[i + j] += x * y
    return _trim(result)


def _divide_by_4u_minus_1(a):
    """Polynomial long division, including an explicit zero-remainder check."""
    remainder = a.copy()
    quotient = [Fraction(0)] * max(1, len(a) - 1)
    for i in range(len(a) - 1, 0, -1):
        quotient[i - 1] = remainder[i] / 4
        remainder[i] -= 4 * quotient[i - 1]
        remainder[i - 1] += quotient[i - 1]
    require(all(value == 0 for value in remainder),
            "nonzero polynomial remainder on division by 4u-1")
    return _trim(quotient)


def egf_run_polynomials(n):
    """Return complete p_m(u), 0 <= m <= n <= 40, from the branch-free EGF.

    Q=4u+4u^2(exp(z)-1)-1, B=2u exp(z/2)+2u-1,
    h=1+u(exp(z)-1), H=sum (-1)^j z^(2j) Q^j/(16^j(2j)!),
    J=sum (-1)^j z^(2j+1) Q^j/(4*16^j(2j+1)!).
    P=Q(H+BJ)/(h(BH-QJ)). No square root is selected or evaluated.
    Coefficients are computed in Q[u][[z]], then multiplied by m!.
    """
    bounded_integer(n, "n", 0, MAX_N)

    def zero():
        return [[Fraction(0)] for _ in range(n + 1)]

    def add(a, b):
        return [_poly_add(x, y) for x, y in zip(a, b)]

    def scale(a, value):
        return [_poly_scale(x, value) for x in a]

    def multiply(a, b):
        result = zero()
        for i, x in enumerate(a):
            if x != [0]:
                for j, y in enumerate(b[:n + 1 - i]):
                    if y != [0]:
                        result[i + j] = _poly_add(result[i + j],
                                                  _poly_multiply(x, y))
        return result

    def shift(a, k):
        return [[Fraction(0)] for _ in range(k)] + a[:n + 1 - k]

    one = zero()
    one[0] = [Fraction(1)]
    q = [[Fraction(-1), Fraction(4)]] + [
        [Fraction(0), Fraction(0), Fraction(4, factorial(i))]
        for i in range(1, n + 1)]
    b = [[Fraction(-1), Fraction(4)]] + [
        [Fraction(0), Fraction(2, 2**i * factorial(i))]
        for i in range(1, n + 1)]
    h = [[Fraction(1)]] + [
        [Fraction(0), Fraction(1, factorial(i))]
        for i in range(1, n + 1)]
    cosine, sine_over_root, power = zero(), zero(), one
    for j in range(n // 2 + 1):
        cosine = add(cosine, scale(shift(power, 2 * j),
                     Fraction((-1)**j, 16**j * factorial(2 * j))))
        if 2 * j + 1 <= n:
            sine_over_root = add(sine_over_root,
                scale(shift(power, 2 * j + 1),
                      Fraction((-1)**j, 4 * 16**j * factorial(2 * j + 1))))
        if j < n // 2:
            power = multiply(power, q)
    numerator = multiply(q, add(cosine, multiply(b, sine_over_root)))
    denominator = multiply(h, add(multiply(b, cosine),
                                  scale(multiply(q, sine_over_root), -1)))
    series, rows = [], []
    for m in range(n + 1):
        residual = numerator[m]
        for i in range(1, m + 1):
            residual = _poly_add(residual, _poly_scale(
                _poly_multiply(denominator[i], series[m - i]), -1))
        coefficient = _divide_by_4u_minus_1(residual)
        series.append(coefficient)
        row = _poly_scale(coefficient, factorial(m))
        require(all(value.denominator == 1 and value >= 0 for value in row),
                f"EGF row {m} is not a nonnegative integral polynomial")
        require(len(row) <= m + 1, f"EGF row {m} has degree above {m}")
        rows.append([int(value) for value in row])
    return rows


def endpoint_run_polynomials(n):
    """Independent integer implementation of CGP Eq. (3), author-PDF p.4.

    Prefix sums in endpoint coordinates implement the published recurrence;
    the run index advances by one whenever a final block is appended. Does not
    call the EGF extraction, literal pop-stack map, or fixed-k fixtures.
    """
    bounded_integer(n, "n", 0, MAX_N)
    zero = [0] * (n + 1)
    prefixes, totals = [None], [[1]]

    def prefix(m, a, b):
        if m < 1 or a < 1 or b < 1:
            return zero
        return prefixes[m][min(a, m)][min(b, m)]

    for m in range(1, n + 1):
        f = [[[0] * (n + 1) for _ in range(m + 1)]
             for _ in range(m + 1)]
        for c in range(1, m + 1):
            for d in range(c, m + 1):
                value = f[c][d]
                value[1] = int(c == 1 and d == m)
                if c == d:
                    x = prefix(m - 1, c - 1, m - 1)
                    y = prefix(m - 1, c - 1, c - 1)
                    for k in range(1, m + 1):
                        value[k] += x[k - 1] - y[k - 1]
                else:
                    for ell in range(d - c):
                        smaller = m - ell - 2
                        multiplier = comb(d - c - 1, ell)
                        x = prefix(smaller, d - ell - 2, smaller)
                        y = prefix(smaller, d - ell - 2, c - 1)
                        for k in range(1, m + 1):
                            value[k] += multiplier * (x[k - 1] - y[k - 1])
        g = [[[0] * (n + 1) for _ in range(m + 1)]
             for _ in range(m + 1)]
        for a in range(1, m + 1):
            for b in range(1, m + 1):
                g[a][b] = [f[a][b][k] + g[a - 1][b][k]
                           + g[a][b - 1][k] - g[a - 1][b - 1][k]
                           for k in range(n + 1)]
        prefixes.append(g)
        totals.append(_trim(g[m][m].copy()))
    return totals


def pop_stack_image(permutation):
    """Push/flush one validated permutation of [m], with 0 <= m <= 9."""
    if not isinstance(permutation, (list, tuple)):
        raise ValueError("permutation must be a list or tuple")
    bounded_integer(len(permutation), "permutation length", 0, MAX_LITERAL_N)
    p = tuple(permutation)
    if (any(type(x) is not int for x in p)
            or sorted(p) != list(range(1, len(p) + 1))):
        raise ValueError("input must be a permutation of 1,...,m")
    return _pop_stack_image(p)


def _pop_stack_image(p):
    stack, output = [], []
    for x in p:
        if stack and x > stack[-1]:
            while stack:
                output.append(stack.pop())
        stack.append(x)
    while stack:
        output.append(stack.pop())
    return tuple(output)


def literal_run_polynomials(n):
    """Deduplicate literal push/flush images of every input, up to n <= 9.

    Counts distinct outputs equally, not the push-forward distribution of a
    uniform input. No overlap characterization is used in this implementation.
    """
    bounded_integer(n, "literal_n", 0, MAX_LITERAL_N)
    rows = [[1]]
    for m in range(1, n + 1):
        images = {_pop_stack_image(p)
                  for p in permutations(range(1, m + 1))}
        counts = [0] * (m + 1)
        for p in images:
            runs = 1 + sum(p[i] > p[i + 1] for i in range(m - 1))
            counts[runs] += 1
        rows.append(_trim(counts))
    return rows


# Expanded, ascending-power numerators from ABH (2021), printed p.10.
# The primary published source and frozen-source SHA-256 are in PROVENANCE.md.
_FIXED_NUMERATORS = {
    1: (0, 1),
    2: (0, 0, 0, 2),
    3: (0, 0, 0, 0, 2, 6, -12),
    4: (0, 0, 0, 0, 0, 0, 42, -148, 10, 360, -288),
    5: (0, 0, 0, 0, 0, 0, 0, 42, 396, -7712, 37964, -81162,
        66120, 25568, -75200, 34560),
}


def fixed_run_numerator(k):
    """Return a fresh list for the published k=1,...,5 numerator fixture."""
    bounded_integer(k, "k", 1, 5)
    return list(_FIXED_NUMERATORS[k])


def fixed_run_denominator(k):
    """Return coefficients of product (1-j*x)^(k-j+1), 1 <= k <= 12.

    This is a denominator representation; no minimality or reduction is claimed.
    """
    bounded_integer(k, "k", 1, MAX_FILTRATION_K)
    denominator = [1]
    for j in range(1, k + 1):
        for _ in range(k - j + 1):
            denominator = _poly_multiply(denominator, [1, -j])
    return [int(value) for value in denominator]


def _validate_triangle(rows):
    if not isinstance(rows, list) or not rows:
        raise ValueError("rows must be a nonempty list")
    bounded_integer(len(rows) - 1, "triangle n", 0, MAX_N)
    for m, row in enumerate(rows):
        if (not isinstance(row, list) or not 1 <= len(row) <= m + 1
                or any(type(x) is not int or x < 0 for x in row)):
            raise ValueError(f"invalid triangle row {m}")
    if rows[0] != [1]:
        raise ValueError("the empty-permutation row must be [1]")


def check_published_fixed_runs(rows):
    """Check D_k F_k=N_k coefficientwise for all supplied rows and k<=5."""
    _validate_triangle(rows)
    checked = 0
    for k in range(1, 6):
        numerator = fixed_run_numerator(k)
        denominator = fixed_run_denominator(k)
        for n in range(len(rows)):
            lhs = sum(denominator[j] *
                      (rows[n - j][k] if k < len(rows[n - j]) else 0)
                      for j in range(min(n, len(denominator) - 1) + 1))
            rhs = numerator[n] if n < len(numerator) else 0
            require(lhs == rhs, f"published fixed-run fixture failed: k={k}, n={n}")
            checked += 1
    return {"passed": True, "k_values": list(range(1, 6)),
            "coefficient_equations_checked": checked}


def check_run_polynomials(n=12, literal_n=7, include_data=False):
    """Compare the complete EGF and endpoint triangles and independent checks."""
    bounded_integer(n, "n", 0, MAX_N)
    bounded_integer(literal_n, "literal_n", 0, MAX_LITERAL_N)
    if literal_n > n:
        raise ValueError("literal_n must not exceed n")
    egf = egf_run_polynomials(n)
    recurrence = endpoint_run_polynomials(n)
    for m, (a, b) in enumerate(zip(egf, recurrence)):
        require(a == b, f"EGF/endpoint polynomial mismatch at n={m}")
    literal = literal_run_polynomials(literal_n)
    for m, (a, b) in enumerate(zip(egf, literal)):
        require(a == b, f"EGF/literal-image polynomial mismatch at n={m}")
    fixed = check_published_fixed_runs(egf)
    result = {
        "passed": True, "n": n, "literal_n": literal_n,
        "egf_endpoint_complete_rows_checked": n + 1,
        "egf_literal_complete_rows_checked": literal_n + 1,
        "published_fixed_runs": fixed,
        "total_counts": [sum(row) for row in egf],
        "coefficient_convention": "row[n][k] = number of distinct images with k ascending runs",
    }
    if include_data:
        result["run_polynomials"] = egf
        result["literal_run_polynomials"] = literal
    return result
