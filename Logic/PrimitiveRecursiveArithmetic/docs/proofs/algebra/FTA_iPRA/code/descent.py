"""One exact rational Kneser step from the accompanying iPRA proof.

Coefficients are Gaussian rational pairs in ascending order.  Trailing zero
coefficients are allowed.  The degree parameter is the length minus one.
All searches are explicitly bounded; all certificate checks use rational
squared norms.  This is a reference for the local lemma, not an efficient
implementation of the enormous worst-case root-name schedule.
"""
from fractions import Fraction as F
from math import comb
from direction import add, mul, scale, power, norm2, direction

ZERO = (F(0), F(0))


def gaussian(z):
    return F(z[0]), F(z[1])


def evaluate(coefficients, z):
    value = ZERO
    for coefficient in reversed(coefficients):
        value = add(mul(value, z), coefficient)
    return value


def translated(coefficients, z):
    n = len(coefficients) - 1
    return [sum_gaussian(scale(F(comb(j, i)), mul(coefficients[j],
                        power(z, j - i))) for j in range(i, n + 1))
            for i in range(n + 1)]


def sum_gaussian(values):
    result = ZERO
    for value in values:
        result = add(result, value)
    return result


def dyadic(exponent):
    return F(2 ** exponent) if exponent >= 0 else F(1, 2 ** (-exponent))


def coefficient_bit_bound(coefficients):
    return max([1] + [abs(v).bit_length()
                       for coefficient in coefficients for x in coefficient
                       for v in (x.numerator, x.denominator)])


def balanced_radius(coefficients):
    """Return r0 with max |b_i| r0^i <= |b0| < max |b_i|(2r0)^i."""
    n = len(coefficients) - 1
    A2 = norm2(coefficients[0])
    assert A2 > 0 and any(norm2(z) > 0 for z in coefficients[1:])
    norms = [norm2(z) for z in coefficients]

    def fits(exponent):
        r = dyadic(exponent)
        return all(norms[i] * r ** (2 * i) <= A2 for i in range(1, n + 1))

    E = 2 * coefficient_bit_bound(coefficients) + 3
    low, high = -E, E
    assert fits(low) and not fits(high)
    # At most this many bisections reduce the integer interval to length one.
    for _ in range((2 * E).bit_length() + 1):
        if high - low <= 1:
            break
        middle = (low + high) // 2
        if fits(middle):
            low = middle
        else:
            high = middle
    assert high == low + 1 and fits(low) and not fits(high)
    return dyadic(low)


def constants(n):
    assert n >= 1
    D = 2 ** n * 4 ** (2 * n * n)
    return D, F(1) - F(1, 4 * D)


def descent(coefficients, z=ZERO):
    coefficients = list(map(gaussian, coefficients))
    z = gaussian(z)
    n = len(coefficients) - 1
    assert n >= 1 and any(norm2(a) > 0 for a in coefficients[1:])
    b = translated(coefficients, z)
    D, q = constants(n)
    if norm2(b[0]) == 0:
        return {"point": z, "offset": ZERO, "radius": F(0),
                "plateau_center": 0, "index": 0, "contracted": True,
                "radius_certificate": True}
    r0 = balanced_radius(b)
    radii = [r0 / 4 ** j for j in range(2 * n + 1)]
    indices = []
    for r in radii:
        # max keeps the first item on ties: least maximizing positive index.
        indices.append(max(range(1, n + 1),
                           key=lambda i: norm2(b[i]) * r ** (2 * i)))
    centers = [j for j in range(1, 2 * n)
               if indices[j - 1] == indices[j] == indices[j + 1]]
    assert centers
    j = centers[0]
    k = indices[j]
    bk_conjugate = (b[k][0], -b[k][1])
    c = scale(F(-1), mul(b[0], bk_conjugate))
    w = direction(c, k)
    offset = scale(radii[j], w)
    point = add(z, offset)
    contracted = norm2(evaluate(coefficients, point)) <= q * q * norm2(b[0])
    radius_certificate = all(norm2(b[i]) * r0 ** (2 * i) <= norm2(b[0])
                             for i in range(1, n + 1))
    assert contracted and radius_certificate and norm2(offset) <= r0 * r0
    return {"point": point, "offset": offset, "radius": r0,
            "plateau_center": j, "index": k, "contracted": contracted,
            "radius_certificate": radius_certificate}


def concise_result(result):
    """Report exact checks and bit sizes; never print giant rational values."""
    return {"plateau_center": result["plateau_center"], "index": result["index"],
            "contracted": result["contracted"],
            "radius_certificate": result["radius_certificate"],
            "coordinate_bits": coefficient_bit_bound([result["point"]])}
