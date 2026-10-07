"""Exact arithmetic shared by the Report213 finite reproduction scripts."""
from decimal import Decimal, localcontext
from fractions import Fraction
from math import comb
from pathlib import Path
import hashlib
import json

MAX_K = 32
ENUM_K = 8
SELECTED_K = (1, 2, 4, 8, 12, 16, 24, 32)
RESULT_FILES = ("checks.json", "moments.csv", "selected_table.csv", "table.tex")


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


def bells(n):
    b = [1]
    for k in range(n):
        b.append(sum(comb(k, j) * b[j] for j in range(k + 1)))
    return b


def recurrence(n):
    """First-edge recurrence. No stored array is used as an input.

    F[0][0]=1; E[t][q]=sum_j F[t][j] binom(j+q-1,q-1).
    The loop order guarantees that both smaller half-lengths are available.
    Only the triangle t+q<=n is needed for E.
    """
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
            e[k][q] = sum(f[k][j] * comb(j + q - 1, q - 1) for j in range(1, k + 1))
    return f, e


def branch(f, t, q, minimum=0):
    return sum(f[t][j] * comb(j + q - 1, q - 1) for j in range(minimum, t + 1))


def partition_sizes(n):
    """One tuple of block sizes per set partition, including multiplicities."""
    def visit(left, sizes):
        if left == 0:
            yield tuple(sizes)
            return
        for i in range(len(sizes)):
            sizes[i] += 1
            yield from visit(left - 1, sizes)
            sizes[i] -= 1
        sizes.append(1)
        yield from visit(left - 1, sizes)
        sizes.pop()
    yield from visit(n, [])


def multiply_truncated(a, b, degree):
    return [sum(a[j] * b[t - j] for j in range(t + 1)) for t in range(degree + 1)]


def majorant(a, n):
    """G[m,s]=m![x^m z^s] exp(sum_(q>=1,t>=0) a_t C(q+t-1,t)x^q z^t/q!).

    Integer recurrence by the block containing the smallest label.
    Coefficients of total degree above n are never formed.
    """
    g = [[0] * (n + 1) for _ in range(n + 1)]
    g[0][0] = 1
    for m in range(1, n + 1):
        for s in range(n - m + 1):
            g[m][s] = sum(comb(m - 1, q - 1) * a[t] * comb(q + t - 1, t)
                          * g[m - q][s - t]
                          for q in range(1, m + 1) for t in range(s + 1))
    return g


def decimal_ratio(value):
    q = Fraction(value)
    with localcontext() as context:
        context.prec = 70
        return format(Decimal(q.numerator) / Decimal(q.denominator), ".10f")


def exact_ratio(value):
    q = Fraction(value)
    return {"numerator": str(q.numerator), "denominator": str(q.denominator)}
