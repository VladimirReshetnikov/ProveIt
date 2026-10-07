"""All fixed-order saddle coefficients C_{s,j}(v), evaluated exactly.

Inputs v and s must be int or Fraction, with v>0 and s>=0; J is a
nonnegative integer. The result consists solely of Fraction objects.
The formal d represents -i*sqrt(2/D)*u. Gaussian moments are applied only
after forming the exponential series. See Report189 for the proof.
"""
from fractions import Fraction as Q
from math import comb, factorial


def rational(value, name):
    if type(value) not in (int, Q):
        raise ValueError(name + ' must be int or Fraction (not float or bool)')
    return Q(value)


def poly_add(a, b):
    result = a.copy()
    for degree, value in b.items():
        result[degree] = result.get(degree, Q(0)) + value
    return {degree: value for degree, value in result.items() if value}


def poly_mul(a, b):
    result = {}
    for i, x in a.items():
        for j, y in b.items():
            result[i + j] = result.get(i + j, Q(0)) + x * y
    return {degree: value for degree, value in result.items() if value}


def scale(a, value):
    return {degree: coefficient * value for degree, coefficient in a.items()
            if coefficient * value}


def double_factorial(k):
    result = 1
    while k > 0:
        result *= k
        k -= 2
    return result


def coefficients(v, s, J):
    """Return C0,...,CJ by exact harmonic-number/formal-series algebra."""
    v, s = rational(v, 'v'), rational(s, 's')
    if v <= 0 or s < 0:
        raise ValueError('require v>0 and s>=0')
    if type(J) is not int or J < 0:
        raise ValueError('J must be a nonnegative integer (not bool)')
    D = v * v + 3 * v + 1
    alpha = (3 - 2 * s) / 4
    # q(z)=(1-exp(-z))/z; psi(z)=-log(q(z))-s*z.
    M = J + 1
    q = [Q((-1) ** k, factorial(k + 1)) for k in range(M + 1)]
    psi = [Q(0)] * (M + 1)
    for m in range(1, M + 1):
        psi[m] = -q[m] - sum((q[k] * (m - k) * psi[m - k]
                              for k in range(1, m)), Q(0)) / m
    psi[1] -= s
    B = [(Q(0), Q(0))]
    for m in range(1, J + 1):
        B.append((psi[m + 1] / 2,
                  sum((psi[i] * psi[m + 1 - i]
                       for i in range(1, m + 1)), Q(0)) / 4))
    logs = [{} for _ in range(2 * J + 1)]
    for r in range(1, 2 * J + 1):
        j = r + 2
        harmonic = sum((Q(1, k) for k in range(1, j + 1)), Q(0))
        harmonic2 = sum((Q(1, k * k) for k in range(1, j + 1)), Q(0))
        logs[r][r + 2] = (-1) ** j * (v * v + 2 * harmonic * v
                                     + harmonic * harmonic - harmonic2) / 4
        logs[r][r] = alpha * Q((-1) ** r, r)
        for m in range(1, min(J, r // 2) + 1):
            ell = r - 2 * m
            av, constant = B[m]
            logcoef = (sum((comb(m, i) * Q((-1) ** (ell - i + 1), ell - i)
                            for i in range(min(m, ell - 1) + 1)), Q(0))
                       if ell else Q(0))
            term = (av * v + constant) * (comb(m, ell) if ell <= m else 0) - av * logcoef
            logs[r][ell] = logs[r].get(ell, Q(0)) + term
    exps = [{0: Q(1)}]
    for r in range(1, 2 * J + 1):
        polynomial = {}
        for k in range(1, r + 1):
            polynomial = poly_add(polynomial,
                                  scale(poly_mul(logs[k], exps[r - k]), Q(k, r)))
        exps.append(polynomial)
    output = []
    for j in range(J + 1):
        output.append(sum((value * (-2 / D) ** (degree // 2)
                           * double_factorial(degree - 1)
                           for degree, value in exps[2 * j].items()
                           if degree % 2 == 0), Q(0)))
    return output


def c1_formula(v, s=0):
    """The displayed first coefficient, using a separately stated formula."""
    v, s = rational(v, 'v'), rational(s, 's')
    if v <= 0 or s < 0:
        raise ValueError('require v>0 and s>=0')
    D, E, F = v * v + 3 * v + 1, 3 * v * v + 11 * v + 6, 12 * v * v + 50 * v + 35
    alpha = (3 - 2 * s) / 4
    B1 = (s - Q(1, 2)) ** 2 / 4 - v / 48
    return (B1 - alpha * (alpha + 1) / D + alpha * E / D ** 2
            + F / (4 * D ** 2) - 5 * E ** 2 / (12 * D ** 3))
