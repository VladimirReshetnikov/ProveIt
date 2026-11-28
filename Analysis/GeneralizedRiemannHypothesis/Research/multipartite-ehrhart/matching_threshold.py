"""Certify the first nonreal Ehrhart numerator among complete graphs minus matchings."""
from fractions import Fraction
from math import comb, pi, tan


def gamma_coefficients(dimension, edges_removed):
    return [
        comb(2 * j, j) * comb(dimension, 2 * j)
        - (2 * edges_removed if j == 1 else 0)
        for j in range(dimension // 2 + 1)
    ]


def certify_real_simple(dimension, edges_removed):
    """Use integer signs at ordered rationals to isolate every root of Gamma(-x)."""
    coefficients = gamma_coefficients(dimension, edges_removed)
    degree = len(coefficients) - 1
    denominator = 10 ** 9
    homogeneous = [
        coeff * denominator ** (degree - j)
        for j, coeff in enumerate(coefficients)
    ][::-1]

    def scaled_value(numerator):
        value = 0
        for coefficient in homogeneous:
            value = value * (-numerator) + coefficient
        return value

    # Floating-point trig supplies candidate rationals only. Each certificate
    # consists of inequalities in integer arithmetic, including the ordering.
    offsets = [0] + [sign * j for j in range(1, 25) for sign in (1, -1)]
    last = 0
    assert scaled_value(0) > 0
    for j in range(1, degree + 1):
        candidates = []
        for offset in offsets:
            angle = (j + 0.25 + offset / 64) * pi / (dimension + 0.5)
            if angle < pi / 2:
                candidates.append(round(denominator * tan(angle) ** 2 / 4))
        if j == degree:
            candidates.append(denominator * dimension ** 4)
        for numerator in candidates:
            if numerator > last and (-1) ** j * scaled_value(numerator) > 0:
                last = numerator
                break
        else:
            break
    else:
        return degree
    raise ArithmeticError("No full sign certificate found")


def main():
    assert gamma_coefficients(2, 1) == [1, 0]
    checked_intervals = 0
    for dimension in range(3, 169):
        checked_intervals += certify_real_simple(dimension, (dimension + 1) // 2)
    checked_intervals += certify_real_simple(169, 84)
    x = Fraction(-1, 218)
    value = first = second = 0
    for coefficient in reversed(gamma_coefficients(169, 85)):
        value, first, second = (
            value * x + coefficient,
            first * x + value,
            second * x + 2 * first,
        )
    laguerre = first * first - value * second
    assert -13348 < laguerre < -13347
    print("Positive alternating-sign intervals certified:", checked_intervals)
    print("Maximal matching real-rooted for d=2 through 168.")
    print("d=169: M=84 real-rooted; M=85 violates Laguerre at -1/218.")
    print("The lobe comparison in the paper extends each passing case to smaller M.")


if __name__ == "__main__":
    if not __debug__:
        raise RuntimeError("Run with assertions enabled (no -O).")
    main()
