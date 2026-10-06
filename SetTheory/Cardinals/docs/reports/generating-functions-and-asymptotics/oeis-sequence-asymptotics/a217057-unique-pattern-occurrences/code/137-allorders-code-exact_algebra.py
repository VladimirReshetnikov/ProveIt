import sys
if not sys.flags.isolated:
    sys.stderr.write("REJECTED: isolated Python (-I) is required\n")
    raise SystemExit(2)
sys.dont_write_bytecode = True

"""Small exact sparse-polynomial and truncated-series engine (standard library)."""
from fractions import Fraction as F
from math import comb


def require(condition, message):
    if not condition:
        raise ValueError(message)


def constant(value, dimension=2):
    value = F(value)
    return {(0,) * dimension: value} if value else {}


def variable(index, dimension=2):
    powers = [0] * dimension
    powers[index] = 1
    return {tuple(powers): F(1)}


def add(*polys):
    result = {}
    for poly in polys:
        for powers, coefficient in poly.items():
            result[powers] = result.get(powers, F()) + coefficient
    return {powers: coefficient for powers, coefficient in result.items() if coefficient}


def scale(poly, value):
    value = F(value)
    return {powers: coefficient * value for powers, coefficient in poly.items() if coefficient * value}


def multiply(left, right):
    result = {}
    for pa, a in left.items():
        for pb, b in right.items():
            require(len(pa) == len(pb), 'polynomial dimension mismatch')
            p = tuple(x + y for x, y in zip(pa, pb))
            result[p] = result.get(p, F()) + a * b
    return {p: c for p, c in result.items() if c}


def power(poly, exponent, dimension=2):
    require(type(exponent) is int and exponent >= 0, 'nonnegative integer exponent required')
    if poly:
        dimension = len(next(iter(poly)))
    result = constant(1, dimension)
    while exponent:
        if exponent & 1:
            result = multiply(result, poly)
        exponent //= 2
        if exponent:
            poly = multiply(poly, poly)
    return result


def substitute(poly, values):
    return sum((coefficient * prod(F(v) ** p for v, p in zip(values, powers))
                for powers, coefficient in poly.items()), F())


def prod(values):
    result = F(1)
    for value in values:
        result *= value
    return result


def series_add(*series):
    length = max(map(len, series))
    return [add(*(s[j] for s in series if j < len(s))) for j in range(length)]


def series_scale(series, value):
    return [scale(p, value) for p in series]


def series_multiply(left, right, order):
    result = [{} for _ in range(order + 1)]
    for i, a in enumerate(left):
        for j, b in enumerate(right[:max(0, order + 1 - i)]):
            result[i + j] = add(result[i + j], multiply(a, b))
    return result


def series_power(series, exponent, order, dimension=2):
    result = [constant(1, dimension)] + [{} for _ in range(order)]
    for _ in range(exponent):
        result = series_multiply(result, series, order)
    return result


def series_inverse(series, order, dimension=2):
    require(series[0] == constant(1, dimension), 'series constant must equal one')
    result = [constant(1, dimension)]
    for n in range(1, order + 1):
        result.append(scale(add(*(multiply(series[k], result[n-k])
                                  for k in range(1, min(n, len(series)-1)+1))), -1))
    return result


def series_log(series, order, dimension=2):
    require(series[0] == constant(1, dimension), 'log constant must equal one')
    result = [{} for _ in range(order + 1)]
    tail = [{}] + series[1:]
    term = [constant(1, dimension)] + [{} for _ in range(order)]
    for k in range(1, order + 1):
        term = series_multiply(term, tail, order)
        result = series_add(result, series_scale(term, F((-1)**(k+1), k)))
    return result


def series_exp(series, order, dimension=2):
    require(not series[0], 'exp constant must equal zero')
    # n E_n = sum_{k=1}^n k S_k E_{n-k}.
    result = [constant(1, dimension)]
    for n in range(1, order + 1):
        result.append(scale(add(*(scale(multiply(series[k], result[n-k]), k)
                                  for k in range(1, min(n, len(series)-1)+1))), F(1, n)))
    return result


def ordinary_series_product(left, right, order):
    return [sum((left[k] * right[n-k] for k in range(n+1)
                 if k < len(left) and n-k < len(right)), F()) for n in range(order+1)]


def ordinary_series_inverse(series, order):
    require(series[0] == 1, 'ordinary inverse constant must equal one')
    result = [F(1)]
    for n in range(1, order + 1):
        result.append(-sum((series[k] * result[n-k] for k in range(1, min(n, len(series)-1)+1)), F()))
    return result


def rational_strings(values):
    return [str(F(value)) for value in values]
