"""Independent ordinary-subtraction diagnostics for sixth-degree bridge.

Polynomial coefficients and local Taylor coefficients are generated here
from the elementary digamma expansion. The Mellin kernel for lambda_5
is evaluated separately. Values are numerical corroboration, not proofs.
"""
from pathlib import Path
import json
import math

import mpmath as mp

mp.mp.dps = 90
DELTA = mp.mpf(1) / 16
TAYLOR_ORDER = 90


def series_product(left, right, upper):
    result = {}
    for a, av in left.items():
        for b, bv in right.items():
            k = a + b
            if k <= upper:
                result[k] = result.get(k, mp.mpf(0)) + av * bv
    return result


def variable_series(j, upper):
    answer = {-j: mp.mpf((-1) ** j * math.factorial(j - 1))}
    for k in range(upper + 1):
        if j == 1 and k == 0:
            answer[k] = mp.mpf(0)  # y = psi + EulerGamma
        else:
            answer[k] = ((-1) ** (j + k) * mp.rf(k + 1, j - 1)
                         * mp.zeta(j + k))
    return answer


def finite_part(terms, weight):
    """terms is [(coefficient, tuple_of_variable_weights), ...]."""
    upper = TAYLOR_ORDER + weight
    variables = {j: variable_series(j, upper) for j in range(1, weight + 1)}
    series = {}
    for coefficient, factors in terms:
        part = {0: mp.mpf(coefficient)}
        for j in factors:
            part = series_product(part, variables[j], upper)
        for k, value in part.items():
            if k <= TAYLOR_ORDER:
                series[k] = series.get(k, mp.mpf(0)) + value

    def ordinary(x):
        vals = {1: mp.digamma(x) + mp.euler}
        for j in range(2, weight + 1):
            vals[j] = mp.polygamma(j - 1, x)
        value = mp.fsum(coefficient * mp.fprod(vals[j] for j in factors)
                        for coefficient, factors in terms)
        principal = mp.fsum(value * x ** k for k, value in series.items() if k < 0)
        return value - principal

    near = mp.fsum(value * DELTA ** (k + 1) / (k + 1)
                   for k, value in series.items() if k >= 0)
    ordinary_integral = near + mp.quad(ordinary, [DELTA, mp.mpf("0.25"), mp.mpf("0.5"), 1])
    cutoff_constant = mp.fsum(value / (k + 1)
                             for k, value in series.items() if k < -1)
    return ordinary_integral + cutoff_constant, {
        str(-k): mp.nstr(v, 65) for k, v in sorted(series.items())
        if k < 0 and abs(v) > mp.mpf("1e-75")}


def mellin_difference(depth):
    epsilon = mp.mpf("1e-60")

    def low(v):
        reference = -mp.log(v)
        increment = -mp.log(-mp.expm1(-v) / v)
        value = reference + increment
        difference = increment * mp.fsum(value ** j * reference ** (depth - 1 - j)
                                         for j in range(depth))
        return difference / v

    def high(v):
        value = -mp.log1p(-mp.exp(-v))
        return value ** depth / v

    integral = mp.quad(low, [epsilon, mp.mpf("1e-4"), mp.mpf("0.01"), mp.mpf("0.1"), 1])
    integral += mp.quad(high, [1, 2, 5, 10, 20, mp.inf])
    return integral


def main():
    z = {k: mp.zeta(k) for k in range(2, 8)}
    P6_terms = [
        (1, (1,) * 6), (15 * z[2], (1,) * 4), (40 * z[3], (1,) * 3),
        (45 * z[2] ** 2 + 90 * z[4], (1, 1)),
        (120 * z[2] * z[3] + 144 * z[5], (1,)),
        (15 * z[2] ** 3 + 90 * z[2] * z[4] + 40 * z[3] ** 2 + 120 * z[6], ())]
    p6, p6_principal = finite_part(P6_terms, 6)
    mixed6, mixed_principal = finite_part([(1, (1, 1, 2, 2))], 6)
    square1, _ = finite_part([(1, (2, 2))], 4)
    square2, _ = finite_part([(1, (3, 3))], 6)
    square1_expected = 2 * z[3] + 4 * mp.diff(mp.zeta, 3)
    square2_expected = -28 * z[5] - 48 * mp.diff(mp.zeta, 5)
    I5 = mellin_difference(5)
    sixth_expected = (-6 * I5 + 15 * mixed6 + 60 * z[2] * mp.diff(mp.zeta, 3)
                       + 48 * mp.diff(mp.zeta, 5) + 90 * z[2] * z[3] + 270 * z[5])
    assert abs(square1 - square1_expected) < mp.mpf("1e-65")
    assert abs(square2 - square2_expected) < mp.mpf("1e-65")
    # The omitted interval (0,1e-60) in I5 contributes about 1e-51;
    # retain a conservative numerical comparison threshold.
    assert abs(p6 - sixth_expected) < mp.mpf("1e-45")
    payload = {
        "method": "ordinary grouped subtraction plus local Taylor integration; independent Mellin kernel",
        "status": "numeric diagnostics passed",
        "mpmath_dps": mp.mp.dps, "taylor_order": TAYLOR_ORDER,
        "local_interval": str(DELTA), "mellin_lower_cutoff": "1e-60",
        "P6_finite_part": mp.nstr(p6, 70),
        "mixed6_finite_part": mp.nstr(mixed6, 70),
        "M6_principal_part": mixed_principal,
        "P6_principal_part": p6_principal,
        "Mellin_I5": mp.nstr(I5, 70),
        "canonical_sixth_absolute_error": mp.nstr(abs(p6 - sixth_expected), 12),
        "square1_value": mp.nstr(square1, 70),
        "square1_absolute_error": mp.nstr(abs(square1 - square1_expected), 12),
        "square2_value": mp.nstr(square2, 70),
        "square2_absolute_error": mp.nstr(abs(square2 - square2_expected), 12),
        "note": "Diagnostics support exact proofs; no certified interval arithmetic is claimed."
    }
    output = Path(__file__).resolve().parent.parent / "results" / "differential_numeric.json"
    output.write_text(json.dumps(payload, indent=2) + "\n")
    print(json.dumps(payload, indent=2))


if __name__ == "__main__":
    main()
