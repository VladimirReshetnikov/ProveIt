"""Exact standard-library arithmetic for Report214's finite checks."""
from decimal import Decimal, localcontext, ROUND_HALF_EVEN
from fractions import Fraction
from math import comb, factorial
from pathlib import Path
import hashlib
import json

MAX_K = 32
ENUM_K = 7
MAX_H = 6
SELECTED_K = (2, 4, 8, 12, 16, 24, 32)
RESULT_FILES = ("checks.json", "selected_table.csv", "polynomials.json", "table.tex", "rows.tex")


def require(condition, name, context=None):
    if not condition:
        raise RuntimeError(f"CHECK_FAILED[{name}]: {context!r}")


def json_bytes(value):
    return (json.dumps(value, indent=2, sort_keys=True, ensure_ascii=True) + "\n").encode("utf-8")


def unique_json(path):
    def pairs(items):
        result = {}
        for key, value in items:
            require(key not in result, "json_duplicate", key)
            result[key] = value
        return result
    return json.loads(Path(path).read_text(encoding="utf-8"), object_pairs_hook=pairs)


def sha256(data):
    return hashlib.sha256(data).hexdigest()


def falling(x, h):
    value = 1
    for i in range(h):
        value *= x - i
    return value


def rising(x, h):
    value = 1
    for i in range(h):
        value *= x + i
    return value


def bells(n):
    result = [1]
    for k in range(n):
        result.append(sum(comb(k, j) * result[j] for j in range(k + 1)))
    return result


def recurrence(n):
    """Fresh first-edge recurrence; no stored row is an input."""
    f = [[0] * (n + 1) for _ in range(n + 1)]
    e = [[0] * (n + 1) for _ in range(n + 1)]
    f[0][0] = 1
    for q in range(1, n + 1):
        e[0][q] = 1
    for k in range(1, n + 1):
        for q in range(1, k + 1):
            for t in range(k - q + 1):
                b = k - q - t
                for j in range(b + 1):
                    f[k][q + j] += e[t][q] * f[b][j] * comb(q + j - 1, q - 1)
        for q in range(1, n - k + 1):
            e[k][q] = sum(f[k][j] * comb(j + q - 1, j) for j in range(k + 1))
    return f, e


def branch(f, t, q):
    """Polynomial expression also defined at q=0; no negative binomial indices."""
    return sum(Fraction(f[t][j] * rising(q, j), factorial(j)) for j in range(t + 1))


def profiles(n, least=1):
    """Integer partition profiles; their set-partition multiplicity is separate."""
    if n == 0:
        yield ()
    for q in range(least, n + 1):
        for rest in profiles(n - q, q):
            yield (q,) + rest


def multiplicity(qs):
    from collections import Counter
    denominator = 1
    for q in qs:
        denominator *= factorial(q)
    for count in Counter(qs).values():
        denominator *= factorial(count)
    return factorial(sum(qs)) // denominator


def compositions(s, r):
    if r == 1:
        yield (s,)
        return
    for t in range(s + 1):
        for rest in compositions(s - t, r - 1):
            yield (t,) + rest


def polynomial_product(a, b):
    out = [Fraction(0)] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            out[i + j] += x * y
    return out


def polynomial_value(coefficients, x):
    result = Fraction(0)
    for coefficient in reversed(coefficients):
        result = result * x + coefficient
    return result


def falling_coefficients(values):
    """Delta^h f(0)/h!, from finitely many values, in the falling basis."""
    row = list(map(Fraction, values))
    result = []
    h = 0
    while row:
        result.append(row[0] / factorial(h))
        row = [row[j + 1] - row[j] for j in range(len(row) - 1)]
        h += 1
    return result


def falling_to_monomial(coefficients):
    result = [Fraction(0)] * len(coefficients)
    basis = [Fraction(1)]
    for u, coefficient in enumerate(coefficients):
        for degree, value in enumerate(basis):
            result[degree] += coefficient * value
        basis = polynomial_product(basis, [-u, 1])
    return result


def signed_stirling_first(n):
    row = [1]
    for r in range(n):
        nxt = [0] * (len(row) + 1)
        for j, value in enumerate(row):
            nxt[j] -= r * value
            nxt[j + 1] += value
        row = nxt
    return row


def shifted_bell(n, r, bell):
    return sum(comb(n, t) * r ** (n - t) * bell[t] for t in range(n + 1))


def exact_ratio(value):
    q = Fraction(value)
    return {"numerator": str(q.numerator), "denominator": str(q.denominator)}


def decimal_ratio(value):
    q = Fraction(value)
    with localcontext() as context:
        context.prec = max(70, len(str(abs(q.numerator))) + len(str(q.denominator)) + 20)
        context.rounding = ROUND_HALF_EVEN
        return format(Decimal(q.numerator) / Decimal(q.denominator), ".6f")
