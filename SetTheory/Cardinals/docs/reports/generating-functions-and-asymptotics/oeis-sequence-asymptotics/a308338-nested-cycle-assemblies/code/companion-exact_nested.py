"""Bounded, exact counts for the Report 167 nested-cycle model.

No network access, floating arithmetic, import-time calculations, or assertions.
The public size limits are deliberately finite; they are not complexity claims.
"""
from bisect import bisect_left
from fractions import Fraction
from itertools import permutations
from math import comb, factorial

MAX_N = 100
MAX_POWER_N = 30
MAX_LITERAL_N = 7


class CheckFailure(RuntimeError):
    """An explicit mathematical check failed (also active under python -O)."""


def require_size(n, maximum=MAX_N, name="n"):
    if type(n) is not int or not 0 <= n <= maximum:
        raise ValueError(f"{name} must be an integer in 0..{maximum}; bool is excluded")
    return n


def check(condition, message):
    if not condition:
        raise CheckFailure(message)


def _integer(value, label):
    value = Fraction(value)
    check(value.denominator == 1, f"nonintegral coefficient: {label}")
    return value.numerator


def component_counts(n):
    """B[j] = j! [z^j] product_m (1+z^m/m), by a labeled cycle product."""
    require_size(n)
    result = [1] + [0] * n
    for m in range(1, n + 1):
        cyclic_orders = factorial(m - 1)
        # Descending updates permit a given cycle length at most once.
        for size in range(n, m - 1, -1):
            result[size] += comb(size, m) * cyclic_orders * result[size - m]
    return result


def _bell_triangle(base):
    n = len(base) - 1
    rows = [[1]]
    for size in range(1, n + 1):
        row = [0] * (size + 1)
        # Choose the component containing the least label.
        for m in range(1, size + 1):
            factor = comb(size - 1, m - 1) * base[m]
            for k, value in enumerate(rows[size - m]):
                row[k + 1] += factor * value
        rows.append(row)
    return rows


def nested_triangle(n):
    """Return rows T[j][k], including T[0][0]=1 and zero column k=0."""
    require_size(n)
    return _bell_triangle(component_counts(n))


def nested_counts(n):
    """Scalar least-label assembly recurrence, independent of triangle summing."""
    require_size(n)
    base = component_counts(n)
    result = [1]
    for size in range(1, n + 1):
        result.append(sum(comb(size - 1, m - 1) * base[m] * result[size - m]
                          for m in range(1, size + 1)))
    return result


def rational_component_series(n):
    """p[j]=[z^j]P from its divisor-sum logarithmic derivative, in Q[[z]]."""
    require_size(n)
    nu = [Fraction(0) for _ in range(n + 1)]
    # z P'/P = sum_r nu[r] z^r,
    # nu[r] = sum_{d|r} (-1)^(r/d-1) / d^(r/d-1).
    for d in range(1, n + 1):
        for q in range(1, n // d + 1):
            nu[d * q] += Fraction((-1) ** (q - 1), d ** (q - 1))
    p = [Fraction(1)]
    for size in range(1, n + 1):
        p.append(sum((nu[m] * p[size - m] for m in range(1, size + 1)),
                     Fraction(0)) / size)
    return p


def rational_egf_counts(n):
    """Return (B,a) from two exact rational differential recurrences."""
    require_size(n)
    p = rational_component_series(n)
    f = [Fraction(1)]
    for size in range(1, n + 1):
        f.append(sum((m * p[m] * f[size - m] for m in range(1, size + 1)),
                     Fraction(0)) / size)
    base = [_integer(factorial(j) * p[j], f"B[{j}]") for j in range(n + 1)]
    counts = [_integer(factorial(j) * f[j], f"a[{j}]") for j in range(n + 1)]
    return base, counts


def rational_power_triangle(n):
    """T[j][k]=j![z^j](P-1)^k/k!, by explicit truncated convolutions."""
    require_size(n, MAX_POWER_N)
    q = rational_component_series(n)
    q[0] = Fraction(0)
    rows = [[0] * (j + 1) for j in range(n + 1)]
    rows[0][0] = 1
    power = [Fraction(1)] + [Fraction(0)] * n
    for k in range(1, n + 1):
        new = [Fraction(0)] * (n + 1)
        for i in range(k - 1, n):
            if power[i]:
                for j in range(1, n - i + 1):
                    new[i + j] += power[i] * q[j]
        power = new
        for size in range(k, n + 1):
            rows[size][k] = _integer(factorial(size) * power[size] / factorial(k),
                                     f"T[{size},{k}]")
    return rows


def _cycle_lengths(permutation):
    seen = set()
    lengths = []
    for start in range(len(permutation)):
        if start in seen:
            continue
        current = start
        length = 0
        while current not in seen:
            seen.add(current)
            length += 1
            current = permutation[current]
        lengths.append(length)
    return lengths


def _cycle_group_histogram(lengths):
    # An underlying permutation supplies distinct labeled cycles. Partition
    # these cycles into unordered blocks, each with no repeated cycle length.
    histogram = [0] * (len(lengths) + 1)
    groups = []

    def visit(index):
        if index == len(lengths):
            histogram[len(groups)] += 1
            return
        length = lengths[index]
        for group in groups:
            if length not in group:
                group.add(length)
                visit(index + 1)
                group.remove(length)
        groups.append({length})
        visit(index + 1)
        groups.pop()

    visit(0)
    return histogram


def literal_nested_triangle(n):
    """Literal permutations plus admissible set partitions of their cycles."""
    require_size(n, MAX_LITERAL_N)
    rows = []
    for size in range(n + 1):
        row = [0] * (size + 1)
        for permutation in permutations(range(size)):
            for k, value in enumerate(_cycle_group_histogram(_cycle_lengths(permutation))):
                row[k] += value
        rows.append(row)
    return rows


def exact_moments(n):
    """Return exact rational mean and variance for a uniform size-n object."""
    require_size(n)
    row = nested_triangle(n)[n]
    total = sum(row)
    mean = Fraction(sum(k * value for k, value in enumerate(row)), total)
    second = Fraction(sum(k * k * value for k, value in enumerate(row)), total)
    return {"mean": mean, "variance": second - mean * mean}


def exact_inverse(y, n=MAX_N):
    """Least 0<=j<=n with a[j]>=positive integer y, or a bounded-range error.

    This performs an exact threshold comparison. No asymptotic rounding is used.
    The empty extension gives N(1)=0 since a[0]=a[1]=1.
    """
    require_size(n)
    if type(y) is not int or y < 1:
        raise ValueError("y must be a positive integer; bool is excluded")
    counts = nested_counts(n)
    index = bisect_left(counts, y)
    if index == len(counts):
        raise ValueError(f"threshold exceeds a[{n}]; no answer within this bounded range")
    return index
