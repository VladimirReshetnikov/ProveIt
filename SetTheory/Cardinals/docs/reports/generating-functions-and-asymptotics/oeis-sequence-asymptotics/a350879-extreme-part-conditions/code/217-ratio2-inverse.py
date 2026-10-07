"""Exact formal inverse polynomials in w, alpha_1,...,alpha_J.

P_j=[u^j](log S-sum_(r=1)^j alpha_r*u^r*S^(-r)),
S=1+u*w+sum_(i<j) P_i*u^(i+1). Coefficients are Fractions.
"""
from fractions import Fraction
from math import comb
from exact import natural


def add(a, b):
    out = dict(a)
    for key, value in b.items():
        out[key] = out.get(key, Fraction(0))+value
        if not out[key]:
            del out[key]
    return out


def scale(a, value):
    return {key: coefficient*value for key, coefficient in a.items() if coefficient*value}


def multiply(a, b):
    out = {}
    for x, v in a.items():
        for y, w in b.items():
            key = tuple(i+j for i, j in zip(x, y))
            out[key] = out.get(key, Fraction(0))+v*w
    return {key: value for key, value in out.items() if value}


def smul(a, b, degree):
    natural(degree, 'degree')
    out = [{} for _ in range(degree+1)]
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            if i+j <= degree:
                out[i+j] = add(out[i+j], multiply(x, y))
    return out


def series_function(series, degree, exponent=None):
    """log(series) if exponent is None, otherwise series**exponent, with S(0)=1."""
    natural(degree, 'degree')
    if not series or len(series[0]) != 1:
        raise ValueError('formal series must start with constant one')
    zero_key = next(iter(series[0]))
    if any(zero_key) or series[0][zero_key] != 1:
        raise ValueError('formal series must start with constant one')
    if exponent is not None and (type(exponent) is not int or exponent >= 0):
        raise ValueError('formal power exponent must be a negative integer')
    v = [{}]+list(series[1:degree+1])
    v += [{} for _ in range(degree+1-len(v))]
    power = [series[0]]+[{} for _ in range(degree)]
    out = [{} for _ in range(degree+1)]
    if exponent is not None:
        out[0] = series[0]
    for k in range(1, degree+1):
        power = smul(power, v, degree)
        scalar = Fraction((-1)**(k+1), k) if exponent is None else Fraction((-1)**k*comb(-exponent+k-1, k))
        for n in range(degree+1):
            out[n] = add(out[n], scale(power[n], scalar))
    return out


def inverse_polynomials(order):
    natural(order)
    width = order+1
    zero = (0,)*width
    one = {zero: Fraction(1)}
    def variable(index):
        key = list(zero)
        key[index] = 1
        return {tuple(key): Fraction(1)}
    series = [one, variable(0)]+[{} for _ in range(order)]
    polynomials = []
    for j in range(1, order+1):
        polynomial = series_function(series, j)[j]
        for r in range(1, j+1):
            term = multiply(variable(r), series_function(series, j-r, -r)[j-r])
            polynomial = add(polynomial, scale(term, -1))
        polynomials.append(polynomial)
        series[j+1] = polynomial
    # Verify the defining logarithmic equation, coefficient by coefficient.
    logseries = series_function(series, order)
    for j in range(1, order+1):
        residual = add(series[j+1], scale(logseries[j], -1))
        for r in range(1, j+1):
            residual = add(residual, multiply(variable(r), series_function(series, order-r, -r)[j-r]))
        if residual:
            raise ArithmeticError('inverse recurrence residual is nonzero')
    return polynomials


def records(polynomials):
    return [[{'powers_w_alpha': list(key), 'coefficient': str(value)}
             for key, value in sorted(poly.items(), reverse=True)] for poly in polynomials]
