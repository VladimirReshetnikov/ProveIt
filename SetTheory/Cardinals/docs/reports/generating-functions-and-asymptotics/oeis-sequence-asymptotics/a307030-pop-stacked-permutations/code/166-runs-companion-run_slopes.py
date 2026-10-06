"""Exact rational enclosures for the root and run-count slope expressions.

This certifies arithmetic inequalities, conditional on the slope formulas and
root identification proved in Report 166. It does not prove a limit theorem,
root uniqueness/dominance, or an effective asymptotic error bound.
"""

from fractions import Fraction
from math import isqrt

from run_polynomials import require

_EXP_TERMS = 200
_TRIG_LAST_INDEX = 60
_SQRT_SCALE = 10**120
_RHO_LOWER = Fraction('1.11343904173672704376166152691808324014139016583344946615')
_RHO_UPPER = Fraction('1.11343904173672704376166152691808324014139016583344946616')


def _add(a, b):
    return a[0] + b[0], a[1] + b[1]


def _subtract(a, b):
    return a[0] - b[1], a[1] - b[0]


def _multiply(a, b):
    candidates = [x * y for x in a for y in b]
    return min(candidates), max(candidates)


def _divide(a, b):
    require(0 < b[0] <= b[1], "interval division requires a positive denominator")
    return _multiply(a, (1 / b[1], 1 / b[0]))


def _fixed(value):
    return Fraction(value), Fraction(value)


def _exp_point(x):
    require(0 <= x < _EXP_TERMS + 2, "exp tail bound outside its domain")
    term = total = Fraction(1)
    for n in range(1, _EXP_TERMS + 1):
        term *= x / n
        total += term
    next_term = term * x / (_EXP_TERMS + 1)
    return total, total + next_term / (1 - x / (_EXP_TERMS + 2))


def _exp_interval(x):
    require(x[0] <= x[1], "reversed exponential interval")
    return _exp_point(x[0])[0], _exp_point(x[1])[1]


def _sqrt_point(x):
    require(x >= 0, "sqrt interval requires a nonnegative argument")
    scale_squared = _SQRT_SCALE**2
    integer = isqrt(x.numerator * scale_squared // x.denominator)
    require(Fraction(integer**2, scale_squared) <= x
            < Fraction((integer + 1)**2, scale_squared),
            "integer-square-root enclosure failed")
    return Fraction(integer, _SQRT_SCALE), Fraction(integer + 1, _SQRT_SCALE)


def _sqrt_interval(x):
    require(x[0] <= x[1], "reversed square-root interval")
    return _sqrt_point(x[0])[0], _sqrt_point(x[1])[1]


def _trig_point(x, sine):
    require(0 <= x <= 1, "trigonometric tail bound outside [0,1]")
    require(_TRIG_LAST_INDEX % 2 == 0, "last trigonometric index must be even")
    term = total = x if sine else Fraction(1)
    for k in range(1, _TRIG_LAST_INDEX + 1):
        a = 2 * k if sine else 2 * k - 1
        term *= -x * x / (a * (a + 1))
        total += term
    a = 2 * (_TRIG_LAST_INDEX + 1) if sine else 2 * (_TRIG_LAST_INDEX + 1) - 1
    next_magnitude = term * x * x / (a * (a + 1))
    return total - next_magnitude, total


def _sin_interval(x):
    require(0 <= x[0] <= x[1] <= 1, "sin monotonicity range exceeded")
    return _trig_point(x[0], True)[0], _trig_point(x[1], True)[1]


def _cos_interval(x):
    require(0 <= x[0] <= x[1] <= 1, "cos monotonicity range exceeded")
    return _trig_point(x[1], False)[0], _trig_point(x[0], False)[1]


def _denominator(x):
    e = _exp_interval(_divide(x, _fixed(2)))
    q = _subtract(_multiply(_fixed(4), _exp_interval(x)), _fixed(1))
    r = _sqrt_interval(q)
    theta = _divide(_multiply(x, r), _fixed(4))
    require(0 < theta[0] <= theta[1] < 1, "root-check angle outside (0,1)")
    return _subtract(_multiply(_add(_multiply(_fixed(2), e), _fixed(1)),
                               _cos_interval(theta)),
                     _multiply(r, _sin_interval(theta)))


def _decimal_integer(value, digits):
    sign = '-' if value < 0 else ''
    value = abs(value)
    return sign + str(value // 10**digits) + '.' + str(value % 10**digits).zfill(digits)


def _print_interval(interval, digits=80):
    lower, upper = interval
    require(lower <= upper, "reversed printable interval")
    floor_lower = lower.numerator * 10**digits // lower.denominator
    ceil_upper = -((-upper.numerator * 10**digits) // upper.denominator)
    return [_decimal_integer(floor_lower, digits), _decimal_integer(ceil_upper, digits)]


def _power(interval, n):
    result = _fixed(1)
    for _ in range(n):
        result = _multiply(result, interval)
    return result


def _term(coefficient, *args):
    result = _fixed(coefficient)
    for interval in args:
        result = _multiply(result, interval)
    return result


def _total(*terms):
    result = _fixed(0)
    for interval in terms:
        result = _add(result, interval)
    return result


def certify_slopes():
    """Return a deterministic, JSON-ready certificate; all inequalities checked.

    exp: positive Taylor polynomial and geometric tail, order 200.
    sqrt: integer-square-root enclosure on the 10^-120 lattice.
    sin/cos: alternating-series upper/lower bounds through index 60 on [0,1].
    Each operation after these enclosures is exact Fraction interval arithmetic.
    """
    lower_sign = _denominator(_fixed(_RHO_LOWER))
    upper_sign = _denominator(_fixed(_RHO_UPPER))
    require(lower_sign[0] > 0 and upper_sign[1] < 0,
            "opposite denominator signs at root bracket were not certified")
    bridge_point = Fraction(6, 5)
    bridge_exp = _exp_point(bridge_point)
    require(_RHO_UPPER < bridge_point and bridge_exp[1] < 4,
            "rho < 6/5 < log(4) bridge was not certified")
    z = _RHO_LOWER, _RHO_UPPER
    t = _exp_interval(z)
    mu = _divide(_total(_term(2, t, z), _term(-1, z), _fixed(-1)),
                  _multiply(_multiply(t, z), _add(z, _fixed(2))))
    variance_numerator = _total(
        _term(4, _power(t, 2), _power(z, 3)),
        _term(-3, t, _power(z, 4)), _term(-10, t, _power(z, 3)),
        _term(-2, t, _power(z, 2)), _term(4, t, z), _power(z, 4),
        _term(4, _power(z, 3)), _term(5, _power(z, 2)),
        _term(4, z), _fixed(2))
    variance_denominator = _multiply(
        _multiply(_power(t, 2), _power(z, 2)), _power(_add(z, _fixed(2)), 3))
    variance = _divide(variance_numerator, variance_denominator)
    require(variance_numerator[0] > 0, "positive variance numerator not certified")
    mu_bounds = (
        Fraction('0.442149549188859664032644356798334757622397538813'),
        Fraction('0.442149549188859664032644356798334757622397538814'))
    variance_bounds = (
        Fraction('0.060085550582698280075387627576274309378657258462'),
        Fraction('0.060085550582698280075387627576274309378657258463'))
    require(mu_bounds[0] < mu[0] <= mu[1] < mu_bounds[1],
            "mean slope is not inside the claimed strict rational enclosure")
    require(variance_bounds[0] < variance[0] <= variance[1] < variance_bounds[1],
            "variance slope is not inside the claimed strict rational enclosure")
    return {
        "passed": True,
        "method": "exact Fraction intervals; exp Taylor tail; integer sqrt; alternating trig bounds",
        "rho_bracket": _print_interval(z, 56),
        "D_at_rho_lower": _print_interval(lower_sign),
        "D_at_rho_upper": _print_interval(upper_sign),
        "mu_bracket": _print_interval(mu_bounds, 48),
        "variance_slope_bracket": _print_interval(variance_bounds, 48),
        "mu_propagated": _print_interval(mu, 55),
        "variance_slope_propagated": _print_interval(variance, 55),
        "variance_numerator_positive": True,
        "rho_upper_less_than_6_over_5": True,
        "exp_6_over_5_bracket": _print_interval(bridge_exp, 55),
        "exp_6_over_5_upper_less_than_4": True,
        "scope": "arithmetic certificate; analytic root identification and slope formulas are proved separately",
    }
