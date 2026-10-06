import sys
if not sys.flags.isolated:
    sys.stderr.write('REJECTED: isolated Python (-I) is required before any imports\n')
    raise SystemExit(2)
sys.dont_write_bytecode = True

# Report142: exact, finite checks and a general fixed-order saddle algorithm.
# Importing this module performs no calculations, writes no files, and prints
# nothing. All arithmetic below is integer or Fraction arithmetic. Polynomial
# coefficient lists are in ascending powers; rational strings are canonical.
from fractions import Fraction
from math import comb, factorial
import json


def _require(condition, message):
    """An optimization-safe check: deliberately not a Python assertion."""
    if not condition:
        raise RuntimeError(message)


def _rational(value):
    value = Fraction(value)
    return str(value.numerator) if value.denominator == 1 else str(value)


def _trim(p):
    p = list(p)
    while len(p) > 1 and p[-1] == 0:
        p.pop()
    return p or [Fraction(0)]


def _add(p, q):
    out = [Fraction(0)] * max(len(p), len(q))
    for i, value in enumerate(p):
        out[i] += value
    for i, value in enumerate(q):
        out[i] += value
    return _trim(out)


def _scale(p, value):
    return _trim([value * c for c in p])


def _mul(p, q, limit=None):
    size = len(p) + len(q) - 1
    if limit is not None:
        size = min(size, limit + 1)
    out = [Fraction(0)] * size
    for i, a in enumerate(p):
        if a:
            for j, b in enumerate(q[:max(0, size - i)]):
                if b:
                    out[i + j] += a * b
    return _trim(out)


def _shift(p, offset):
    """Coefficients of p(x + offset)."""
    out = [Fraction(0)]
    for coefficient in reversed(p):
        out = _add(_mul(out, [Fraction(offset), Fraction(1)]), [coefficient])
    return out


def _evaluate(p, x):
    out = Fraction(0)
    for coefficient in reversed(p):
        out = out * x + coefficient
    return out


def _falling(order):
    out = [Fraction(1)]
    for j in range(order):
        out = _mul(out, [Fraction(-j), Fraction(1)])
    return out


def _exact_quotient(p, q):
    remainder = _trim(p)
    quotient = [Fraction(0)] * (max(0, len(p) - len(q)) + 1)
    while len(remainder) >= len(q) and remainder != [0]:
        degree = len(remainder) - len(q)
        value = remainder[-1] / q[-1]
        quotient[degree] += value
        for j, coefficient in enumerate(q):
            remainder[degree + j] -= value * coefficient
        remainder = _trim(remainder)
    _require(remainder == [0], "nonzero polynomial-division remainder")
    return _trim(quotient)


def _power_sums(maximum):
    """Return the exact polynomials sum(i**d, i=0,...,n-1).

    This uses x**d = sum(S(d,j)*(x)_j) and
    sum((i)_j, i=0,...,n-1) = (n)_(j+1)/(j+1).
    """
    out = []
    stirling = [1]
    for degree in range(maximum + 1):
        if degree:
            previous = stirling
            stirling = [0] * (degree + 1)
            for j in range(1, degree + 1):
                stirling[j] = previous[j - 1] + (j * previous[j] if j < len(previous) else 0)
        polynomial = [Fraction(0)]
        for j, coefficient in enumerate(stirling):
            polynomial = _add(polynomial, _scale(_falling(j + 1), Fraction(coefficient, j + 1)))
        out.append(polynomial)
    return out


def top_coefficients(order):
    """Construct c_a(n)=[k**(n-a)]p_n(k), as exact polynomials.

    The discrete increment is (2n-2)c_(a-1)(n-1) plus
    sum_i sum_b c_b(i)c_(a-1-b)(n-1-i). Every finite sum is
    performed polynomially, so this is not numerical interpolation.
    """
    if type(order) is not int or order < 0:
        raise ValueError("order must be a nonnegative integer")
    sums = _power_sums(2 * order)
    coefficients = [[Fraction(1)]]
    for a in range(1, order + 1):
        increment = _mul([Fraction(-2), Fraction(2)], _shift(coefficients[a - 1], -1))
        for b in range(a):
            left = coefficients[b]
            right = coefficients[a - 1 - b]
            for u, left_coefficient in enumerate(left):
                if not left_coefficient:
                    continue
                for v, right_coefficient in enumerate(right):
                    if not right_coefficient:
                        continue
                    # Expand (n-1-i)**v and sum the resulting powers of i.
                    for q in range(v + 1):
                        power = [Fraction(comb(v - q, j) * (-1) ** (v - q - j))
                                 for j in range(v - q + 1)]
                        multiplier = left_coefficient * right_coefficient * comb(v, q) * (-1) ** q
                        increment = _add(increment, _scale(_mul(power, sums[u + q]), multiplier))
        # c_a(n)=sum_{i=0}^{n-1} increment(i+1), fixing c_a(0)=0.
        polynomial = [Fraction(0)]
        for degree, coefficient in enumerate(_shift(increment, 1)):
            polynomial = _add(polynomial, _scale(sums[degree], coefficient))
        coefficients.append(polynomial)
    return coefficients


def _ordinary_polynomials(maximum):
    polynomials = [[1]]
    for n in range(1, maximum + 1):
        out = [0] * (n + 1)
        for degree, value in enumerate(polynomials[n - 1]):
            out[degree] += (2 * n - 2) * value
            out[degree + 1] += value
        for i in range(n):
            for u, a in enumerate(polynomials[i]):
                for v, b in enumerate(polynomials[n - 1 - i]):
                    out[u + v] += a * b
        polynomials.append(out)
    return polynomials


def _top_checks():
    order, maximum = 7, 21
    coefficients = top_coefficients(order)
    polynomials = _ordinary_polynomials(maximum)
    records = []
    boundary_checks = 0
    comparison_checks = 0
    for a, polynomial in enumerate(coefficients):
        _require(len(polynomial) - 1 <= 2 * a, "top-coefficient degree bound failed")
        for n in range(a):
            _require(_evaluate(polynomial, n) == 0, "top-coefficient boundary zero failed")
            boundary_checks += 1
        quotient = _exact_quotient(polynomial, _falling(a))
        _require(len(quotient) - 1 <= a, "falling-factorial quotient degree bound failed")
        for n in range(maximum + 1):
            expected = polynomials[n][n - a] if n >= a else 0
            actual = _evaluate(polynomial, n)
            _require(actual.denominator == 1, "top coefficient is not an integer")
            _require(actual == expected, "top coefficient disagrees with direct recurrence")
            comparison_checks += 1
        records.append({"order": a, "degree": len(polynomial) - 1,
                        "coefficients": [_rational(c) for c in polynomial],
                        "falling_quotient_coefficients": [_rational(c) for c in quotient]})
    return {"maximum_order": order, "maximum_n": maximum,
            "degree_bound_checks": len(coefficients),
            "boundary_zero_checks": boundary_checks,
            "falling_divisibility_checks": len(coefficients),
            "direct_recurrence_checks": comparison_checks,
            "integer_value_checks": comparison_checks, "polynomials": records}


def _gamma(n):
    return Fraction(comb(2 * n, n), 4 ** n)


def _delta(n):
    return _gamma(n) / (2 * n - 1)


def _frozen_checks():
    maximum, direct_maximum = 40, 12
    gamma = [_gamma(n) for n in range(maximum + 1)]
    delta = [Fraction(0)] + [_delta(n) for n in range(1, maximum + 1)]
    binomial = Fraction(1)
    coefficient_checks = 0
    weights = []
    for n in range(1, maximum + 1):
        binomial *= (Fraction(1, 2) - (n - 1)) / n
        _require(-binomial * (-1) ** n == delta[n], "square-root coefficient identity failed")
        weights.append({"degree": n, "gamma": _rational(gamma[n]), "delta": _rational(delta[n])})
        for r in range(n + 1):
            convolution = Fraction(0)
            for i in range(1, n):
                # Explicit second-coordinate convolution, before rational weighting.
                multiplicity = sum(comb(i, c) * comb(n - i, r - c)
                                   for c in range(max(0, r - (n - i)), min(i, r) + 1))
                convolution += delta[i] * gamma[n - i] * multiplicity
            residual = (gamma[n] - delta[n]) * comb(n, r) - convolution
            _require(residual == 0, "frozen inverse basis coefficient failed")
            coefficient_checks += 1
    samples = []
    for s in (Fraction(1, 5), Fraction(1, 2), Fraction(4, 5), Fraction(19, 20)):
        a, b = {}, {}
        for n in range(1, direct_maximum + 1):
            for r in range(n + 1):
                factor = s ** (2 * n + r) * (1 - s) ** (n - r) * comb(n, r)
                a[n, r] = gamma[n] * factor
                b[n, r] = delta[n] * factor
        checks = 0
        for n in range(1, direct_maximum + 1):
            for r in range(n + 1):
                convolution = sum((b[i, c] * a[n - i, r - c]
                                   for i in range(1, n)
                                   for c in range(max(0, r - (n - i)), min(i, r) + 1)), Fraction(0))
                _require(a[n, r] - b[n, r] - convolution == 0, "frozen inverse rational sample failed")
                checks += 1
        samples.append({"s": _rational(s), "maximum_degree": direct_maximum,
                        "coefficient_checks": checks, "maximum_absolute_residual": "0"})
    return {"maximum_degree": maximum, "sqrt_coefficient_checks": maximum,
            "basis_coefficient_checks": coefficient_checks,
            "weights": weights, "samples": samples,
            "direct_coefficient_checks": sum(sample["coefficient_checks"] for sample in samples)}


def _log_series(series, degree):
    _require(series[0] == 1, "formal logarithm requires constant coefficient one")
    series = list(series) + [Fraction(0)] * (degree + 1 - len(series))
    out = [Fraction(0)] * (degree + 1)
    for n in range(1, degree + 1):
        out[n] = series[n] - sum((k * out[k] * series[n - k] for k in range(1, n)), Fraction(0)) / n
    return out


def _saddle_jets(s, degree):
    """Return a_j/j!, kappa_j/j! using formal Taylor arithmetic only.

    With z=t*exp(x), f(z)/f(t)=(1-(t/s**2)*(exp(x)-1))**(-1/2).
    Also h(z)/h(t)=1+(f(z)/f(t)-1)/(1-s).
    """
    t = 1 - s * s
    change = [Fraction(0)] + [t / (s * s * factorial(j)) for j in range(1, degree + 1)]
    power = [Fraction(1)]
    f_ratio = [Fraction(1)]
    for j in range(1, degree + 1):
        power = _mul(power, change, degree)
        f_ratio = _add(f_ratio, _scale(power, _gamma(j)))
    f_ratio += [Fraction(0)] * (degree + 1 - len(f_ratio))
    h_ratio = [Fraction(1)] + [coefficient / (1 - s) for coefficient in f_ratio[1:]]
    return _log_series(f_ratio, degree), _log_series(h_ratio, degree)


def _gaussian_moment(power, variance):
    """Gaussian expectation of (i*u)**power, with u variance 1/B."""
    if power % 2:
        return Fraction(0)
    half = power // 2
    odd_factorial = 1
    for j in range(1, half + 1):
        odd_factorial *= 2 * j - 1
    return Fraction((-1) ** half * odd_factorial) / variance ** half


def saddle_coefficients(s, ell, r, order):
    """Return D_0,...,D_order for any nonnegative fixed order.

    s must be an exact rational in (0,1); integer shifts satisfy 0<=r<=ell.
    The exponent is expanded in z=m**(-1/2), with v=i*u. Its coefficient
    of z**q is (a_q-r*kappa_q+ell*1[q=1])*v**q/q!
    + kappa_(q+2)*v**(q+2)/(q+2)!. The recurrence
    n*E_n=sum(q*P_q*E_(n-q),q=1,...,n) exponentiates it.
    Gaussian moments then give D_j from E_(2j). This is an algorithm at
    arbitrary fixed order, not a numerical integration or remainder bound.
    """
    if isinstance(s, float):
        raise ValueError("s must be exact; use Fraction or a rational string")
    s = Fraction(s)
    if not 0 < s < 1:
        raise ValueError("s must lie strictly between zero and one")
    if any(type(value) is not int for value in (ell, r, order)) or order < 0 or not 0 <= r <= ell:
        raise ValueError("integer arguments must satisfy order>=0 and 0<=r<=ell")
    a, kappa = _saddle_jets(s, 2 * order + 2)
    variance = 2 * kappa[2]
    _require(variance == (1 - s * s) * (s + 2) / (4 * s ** 4), "saddle variance identity failed")
    exponent = [[Fraction(0)]]
    for q in range(1, 2 * order + 1):
        polynomial = [Fraction(0)] * (q + 3)
        polynomial[q] = a[q] - r * kappa[q] + (ell if q == 1 else 0)
        polynomial[q + 2] = kappa[q + 2]
        exponent.append(_trim(polynomial))
    exponential = [[Fraction(1)]]
    for n in range(1, 2 * order + 1):
        polynomial = [Fraction(0)]
        for q in range(1, n + 1):
            polynomial = _add(polynomial, _scale(_mul(exponent[q], exponential[n - q]), Fraction(q, n)))
        exponential.append(polynomial)
        _require(all(coefficient == 0 for power, coefficient in enumerate(polynomial) if power % 2 != n % 2),
                 "saddle parity identity failed")
    return [sum((coefficient * _gaussian_moment(power, variance)
                 for power, coefficient in enumerate(exponential[2 * j])), Fraction(0))
            for j in range(order + 1)]


def _series_quotient(numerator, denominator):
    _require(denominator[0] == 1, "normalized saddle denominator must start at one")
    quotient = []
    for n in range(len(numerator)):
        quotient.append(numerator[n] - sum((denominator[k] * quotient[n - k]
                                            for k in range(1, n + 1)), Fraction(0)))
    return quotient


def _closed_d2(s):
    numerator = (s ** 12 - 14 * s ** 11 + 759 * s ** 10 + 1574 * s ** 9 - 1079 * s ** 8
                 - 4386 * s ** 7 - 1346 * s ** 6 + 4410 * s ** 5 + 4128 * s ** 4
                 - 368 * s ** 3 - 1871 * s ** 2 - 576 * s + 64)
    return numerator / (288 * (s - 1) ** 2 * (s + 1) ** 2 * (s + 2) ** 6)


def _saddle_checks():
    order = 3
    shifts = ((0, 0), (1, 0), (1, 1), (3, 1), (4, 3))
    records = []
    quotient_checks = first_order_checks = zero_shift_checks = closed_d2_checks = 0
    for s in (Fraction(1, 5), Fraction(1, 2), Fraction(4, 5), Fraction(19, 20)):
        base = saddle_coefficients(s, 0, 0, order)
        _require(base[2] == _closed_d2(s), "unshifted D_2 closed-form check failed")
        closed_d2_checks += 1
        a, kappa = _saddle_jets(s, 4)
        variance = 2 * kappa[2]
        third, fourth = 6 * kappa[3], 24 * kappa[4]
        for ell, r in shifts:
            raw = saddle_coefficients(s, ell, r, order)
            normalized = _series_quotient(raw, base)
            first = a[1] - r * kappa[1] + ell
            second = 2 * (a[2] - r * kappa[2])
            closed_d1 = (-(second + first * first) / (2 * variance)
                         + (fourth / 8 + first * third / 2) / variance ** 2
                         - 5 * third * third / (24 * variance ** 3))
            _require(raw[0] == 1 and raw[1] == closed_d1, "first saddle coefficient check failed")
            first_order_checks += 1
            for j in range(order + 1):
                product = sum((base[k] * normalized[j - k] for k in range(j + 1)), Fraction(0))
                _require(product == raw[j], "normalized saddle quotient identity failed")
                quotient_checks += 1
            if ell == 0 and r == 0:
                for j in range(1, order + 1):
                    _require(normalized[j] == 0, "zero-shift normalized coefficient is nonzero")
                    zero_shift_checks += 1
            records.append({"s": _rational(s), "ell": ell, "r": r,
                            "D": [_rational(value) for value in raw],
                            "V": [_rational(value) for value in normalized]})
    return {"maximum_order": order, "sample_count": 4, "shift_count": len(shifts),
            "first_order_formula_checks": first_order_checks,
            "unshifted_second_order_formula_checks": closed_d2_checks,
            "quotient_coefficient_checks": quotient_checks,
            "zero_shift_positive_order_checks": zero_shift_checks, "cases": records}


def run():
    """Return a deterministic, JSON-serializable record of exact finite checks.

    Passing these finite checks is not a proof of analytic uniform remainders
    or an effective numerical error bound for an asymptotic expansion.
    """
    return {"schema_version": 1, "status": "PASS", "arithmetic": "exact rational",
            "top_coefficients": _top_checks(), "frozen_inverse": _frozen_checks(),
            "saddle": _saddle_checks()}


if __name__ == "__main__":
    print(json.dumps(run(), sort_keys=True, indent=2))
