#!/usr/bin/env python3
"""Independent exact checks, using only Python's standard library.

The sparse-polynomial calculation below is deliberately independent of SymPy.
No test uses assert: optimization with python -O cannot disable a check.
"""
from fractions import Fraction
from hashlib import sha256
from math import comb, factorial
import json
from pathlib import Path

F = Fraction
# Ascending numerator coefficients for Q_j, with denominator D_j (1+r)^(3j).
REFERENCE_Q = (
    (1, (1,)),
    (24, (-2, 156, 407, 369, 115)),
    (1152, (4, -624, 41284, 204132, 423789, 472566, 296947, 99366, 13801)),
    (414720, (1112, 19728, -1221468, 79702668, 539959926,
              1610091936, 2782462609, 3039867351, 2142836616,
              946728423, 236469702, 23863023, -660793)),
)
OEIS_PREFIX = (
    1, 1, 3, 12, 59, 338, 2185, 15613, 121553, 1020170,
    9154963, 87276995, 879242215, 9319182044, 103537712361,
    1201967382478, 14540040004755, 182840037042560,
    2384985091689409, 32209645344213417, 449608555748234353,
    6476887237235672388, 96156363230696213447,
)


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def rising(x, k):
    result = F(1)
    for i in range(k):
        result *= x + i
    return result


def add(a, b):
    result = dict(a)
    for degree, value in b.items():
        result[degree] = result.get(degree, F(0)) + value
    return {k: v for k, v in result.items() if v}


def multiply(a, b):
    result = {}
    for i, x in a.items():
        for j, y in b.items():
            result[i+j] = result.get(i+j, F(0)) + x*y
    return result


def double_factorial(k):
    result = 1
    for i in range(k, 0, -2):
        result *= i
    return result


def saddle_correction(r, b, order):
    # Touchard polynomials obtained from the integer Stirling recurrence.
    row = [1]
    p = [F(0)]
    for k in range(1, 2*order + 3):
        row = [0] + [row[i-1] + (i*row[i] if i < len(row) else 0)
                     for i in range(1, k+1)]
        p.append(sum(F(row[i])*r**(i-1) for i in range(1, k+1)))
    exponents = [{}]
    for s in range(1, 2*order + 1):
        exponents.append({s+2: p[s+2]/factorial(s+2), s: -b*r/factorial(s)})
    powers = [{0: F(1)}]
    for k in range(1, 2*order + 1):
        term = {}
        for s in range(1, k+1):
            product = multiply(exponents[s], powers[k-s])
            term = add(term, {d: v*F(s, k) for d, v in product.items()})
        powers.append(term)
    return sum(v*(-1)**(d//2)*double_factorial(d-1)/(1+r)**(d//2)
               for d, v in powers[2*order].items() if d % 2 == 0)


def enumeration(limit):
    row, catalan, values = [1], [1], [1]
    for n in range(1, limit+1):
        row = [0] + [row[k-1] + (k*row[k] if k < len(row) else 0)
                     for k in range(1, n+1)]
        numerator = catalan[-1]*2*(2*n-1)
        require(numerator % (n+1) == 0, 'Catalan recurrence lost integrality')
        catalan.append(numerator//(n+1))
        values.append(sum(x*y for x, y in zip(row, catalan)))
    return values


def ode_enumeration(limit):
    # Coefficients of (e^z-1)F''+(1+5e^z-4e^(2z))F'-2e^(2z)F=0.
    values = [1]
    for n in range(limit):
        rhs = 2*sum(comb(n, j)*2**j*values[n-j] for j in range(n+1))
        rhs -= sum(comb(n, j)*values[n-j+2] for j in range(2, n+1))
        rhs -= sum(comb(n, j)*(5-4*2**j)*values[n-j+1] for j in range(1, n+1))
        require(rhs % (n+2) == 0, 'ODE recurrence lost integrality')
        values.append(rhs//(n+2))
    return values


def run(data_dir=None):
    if data_dir is None:
        data_dir = Path(__file__).resolve().parent/'data'
    exported = json.loads((data_dir/'polynomial_coefficients.json').read_text())
    require(len(exported) == len(REFERENCE_Q), 'Wrong number of Q coefficients')
    c = [sum(rising(F(1, 2), k)*rising(F(3, 2), k)/4**k/factorial(k)
             *rising(F(3, 2)+k, m-k)/factorial(m-k) for k in range(m+1))
         for m in range(4)]
    require(c == [F(1), F(27, 16), F(1245, 512), F(27685, 8192)],
            'Endpoint-to-saddle coefficients differ')
    points = 0
    for j, (denominator, numerator) in enumerate(REFERENCE_Q):
        require(exported[j] == {'degree_bound': 4*j, 'denominator_constant': denominator,
                                'numerator_ascending': list(numerator)},
                f'Exported Q{j} differs from independent literal coefficients')
        for value in range(1, 4*j+2):
            r = F(value)
            actual = sum(c[m]*(4*r)**m*saddle_correction(r, F(3, 2)+m, j-m)
                         for m in range(j+1))
            expected = sum(F(x)*r**k for k, x in enumerate(numerator)) / (
                denominator*(1+r)**(3*j))
            require(actual == expected, f'Exact Q{j} identity fails at r={r}')
            points += 1
    values = enumeration(200)
    require(values == ode_enumeration(200), 'Stirling and ODE enumeration differ')
    require(values[:len(OEIS_PREFIX)] == list(OEIS_PREFIX), 'OEIS prefix differs')
    return {
        'status': 'PASS', 'rational_identity_points': points,
        'highest_correction_order': 3, 'independent_exact_counts_through': 200,
        'oeis_prefix_terms': len(OEIS_PREFIX),
        'a200_sha256': sha256(str(values[-1]).encode()).hexdigest(),
        'test_style': 'explicit exceptions; active under python -O',
    }


if __name__ == '__main__':
    print(json.dumps(run(), indent=2, sort_keys=True))
