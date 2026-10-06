"""A standalone exact-rational interval certificate for the DSASM map bounds.

Only the Python standard library is used. All arithmetic and all comparisons
that establish the certificate use integers or fractions. Decimal strings are
parsed as exact rationals; no binary floating point enters the computation.
Every guard is explicit and therefore remains effective under ``python -O``.

Logarithms are range-reduced into [1, 2] and evaluated using the atanh
series. Exponentials are reduced to [0, 1/8] before a Taylor enclosure and
repeated squaring. Each interval operation is rounded outward to a fixed
rational grid, keeping intermediate integer sizes bounded.
"""

from dataclasses import dataclass
from fractions import Fraction
from functools import lru_cache
import json
import re


DIGITS = 100
SCALE = 10 ** DIGITS
LOG_TERMS = 128
EXP_TERMS = 80
_DECIMAL = re.compile(r"-?(?:0|[1-9][0-9]*)(?:\.[0-9]+)?\Z")
_REQUIRED = frozenset(("p", "q", "width"))
_OPTIONAL = frozenset(("g", "alpha", "b", "theta", "contraction"))

DEFAULT_DISPLAYS = {
    "p": [
        "0.2632463454286169293260401267680",
        "0.2632463454286169293260401267681",
    ],
    "q": [
        "0.2960487268742950122628240495510507",
        "0.2960487268742950122628240495510786",
    ],
    "width": [
        "0.1253798291941521304554959668203247",
        "0.1253798291941521304554959668208131",
    ],
}


def _require(condition, message):
    if not condition:
        raise ValueError("INTERVAL: " + message)


def _fraction(value):
    _require(not isinstance(value, (bool, float)),
             "boolean and binary-floating-point inputs are forbidden")
    _require(isinstance(value, (int, Fraction)),
             "internal arithmetic requires an integer or Fraction")
    return Fraction(value)


def _floor_grid(value):
    return Fraction((value.numerator * SCALE) // value.denominator, SCALE)


def _ceil_grid(value):
    return Fraction(-((-value.numerator * SCALE) // value.denominator), SCALE)


@dataclass(frozen=True)
class Interval:
    """Closed rational interval, outward-rounded after each operation."""

    low: Fraction
    high: Fraction

    def __post_init__(self):
        lo, hi = _fraction(self.low), _fraction(self.high)
        _require(lo <= hi, "interval endpoints are reversed")
        object.__setattr__(self, "low", lo)
        object.__setattr__(self, "high", hi)

    @classmethod
    def point(cls, value):
        value = _fraction(value)
        return cls(value, value)

    @classmethod
    def rounded(cls, low, high):
        return cls(_floor_grid(_fraction(low)), _ceil_grid(_fraction(high)))

    @staticmethod
    def coerce(value):
        return value if isinstance(value, Interval) else Interval.point(value)

    def __add__(self, other):
        other = self.coerce(other)
        return Interval.rounded(self.low + other.low, self.high + other.high)

    __radd__ = __add__

    def __neg__(self):
        return Interval(-self.high, -self.low)

    def __sub__(self, other):
        return self + (-self.coerce(other))

    def __rsub__(self, other):
        return self.coerce(other) + (-self)

    def __mul__(self, other):
        other = self.coerce(other)
        products = (self.low * other.low, self.low * other.high,
                    self.high * other.low, self.high * other.high)
        return Interval.rounded(min(products), max(products))

    __rmul__ = __mul__

    def reciprocal(self):
        _require(self.high < 0 or self.low > 0,
                 "division interval contains zero")
        return Interval.rounded(1 / self.high, 1 / self.low)

    def __truediv__(self, other):
        return self * self.coerce(other).reciprocal()

    def __rtruediv__(self, other):
        return self.coerce(other) * self.reciprocal()


@lru_cache(maxsize=128)
def _reduced_log(value):
    """Enclose log(value) for 1 <= value <= 2 using 128 terms."""
    _require(Fraction(1) <= value <= Fraction(2),
             "reduced logarithm argument is outside [1,2]")
    if value == 1:
        return Interval.point(0)
    ratio = Interval.point((value - 1) / (value + 1))
    ratio_squared = ratio * ratio
    odd_power = ratio
    series = Interval.point(0)
    for index in range(LOG_TERMS):
        series = series + odd_power / (2 * index + 1)
        odd_power = odd_power * ratio_squared
    # For 0 <= z <= 1/3, the omitted tail is at most
    # 2*z^(2N+1)/((2N+1)*(1-z^2)). Use z=1/3 here.
    tail = Fraction(9, 4 * (2 * LOG_TERMS + 1) *
                    3 ** (2 * LOG_TERMS + 1))
    result = 2 * series
    return Interval.rounded(result.low, result.high + tail)


@lru_cache(maxsize=128)
def _log_point(value):
    value = _fraction(value)
    _require(value > 0, "logarithm requires a strictly positive argument")
    shift = 0
    reduced = value
    while reduced < 1:
        reduced *= 2
        shift -= 1
    while reduced > 2:
        reduced /= 2
        shift += 1
    return _reduced_log(reduced) + shift * _reduced_log(Fraction(2))


def log_interval(value):
    value = Interval.coerce(value)
    _require(value.low > 0, "logarithm interval is not strictly positive")
    return Interval(_log_point(value.low).low, _log_point(value.high).high)


@lru_cache(maxsize=128)
def _exp_point(value):
    value = _fraction(value)
    if value == 0:
        return Interval.point(1)
    if value < 0:
        return _exp_point(-value).reciprocal()
    reduced = value
    squarings = 0
    while reduced > Fraction(1, 8):
        reduced /= 2
        squarings += 1
    argument = Interval.point(reduced)
    term = Interval.point(1)
    partial = term
    for index in range(1, EXP_TERMS + 1):
        term = term * argument / index
        partial = partial + term
    # The first omitted term is x^(N+1)/(N+1)!; successive term
    # ratios are bounded above by x/(N+2) < 1.
    first_omitted_upper = term.high * reduced / (EXP_TERMS + 1)
    ratio_upper = reduced / (EXP_TERMS + 2)
    _require(ratio_upper < 1, "exponential tail ratio is not below one")
    tail_upper = first_omitted_upper / (1 - ratio_upper)
    result = Interval.rounded(partial.low, partial.high + tail_upper)
    for unused in range(squarings):
        result = result * result
    return result


def exp_interval(value):
    value = Interval.coerce(value)
    return Interval(_exp_point(value.low).low, _exp_point(value.high).high)


def _parse_display(name, pair):
    _require(type(pair) is list and len(pair) == 2,
             name + " must be a two-element array of decimal strings")
    for text in pair:
        _require(type(text) is str and len(text) <= 250 and
                 _DECIMAL.fullmatch(text) is not None,
                 name + " contains an invalid exact decimal string")
    lo, hi = (Fraction(text) for text in pair)
    _require(lo < hi, name + " decimal endpoints must be strictly increasing")
    return Interval(lo, hi)


def _decimal_bound(value, places, upper):
    _require(type(places) is int and 0 <= places <= DIGITS,
             "invalid decimal display precision")
    scale = 10 ** places
    numerator = value.numerator * scale
    units = (-((-numerator) // value.denominator) if upper else
             numerator // value.denominator)
    sign = "-" if units < 0 else ""
    digits = str(abs(units)).rjust(places + 1, "0")
    if places == 0:
        return sign + digits
    return sign + digits[:-places] + "." + digits[-places:]


def _rational_text(value):
    return str(value.numerator) + "/" + str(value.denominator)


def _record(value):
    return {
        "rational": [_rational_text(value.low), _rational_text(value.high)],
        "decimal_outward": [
            _decimal_bound(value.low, 80, False),
            _decimal_bound(value.high, 80, True),
        ],
    }


def _strictly_inside(name, actual, display):
    _require(display.low < actual.low and actual.high < display.high,
             name + " displayed bounds do not strictly enclose the rational certificate")


def _compute(p):
    log2 = log_interval(2)
    log3 = log_interval(3)
    g = Fraction(3, 2) * log3 - 2 * log2
    alpha = g / 2
    b = (g + log2) / 2
    theta = log3 / (2 * log2)
    slope = (1 - theta) / theta
    contraction = slope / 2
    _require(g.low > 0, "g is not certified positive")
    _require(Fraction(1, 2) < theta.low and theta.high < 1,
             "theta is not certified in (1/2,1)")
    _require(0 < slope.low and slope.high < 1,
             "the affine-map slope magnitude is not in (0,1)")
    _require(0 < contraction.low and contraction.high < 1,
             "contraction factor is not certified in (0,1)")

    def lower_map(x):
        return (b - theta * g - (1 - theta) * x) / theta

    def upper_map(x):
        argument = (3 * exp_interval(2 * (b - x)) - 1) / 2
        return x - g + log_interval(argument) / 2

    j_low, j_high = b - g, b
    _require(j_low.high < p.low and p.high < j_high.low,
             "p bracket is not certified to lie inside J")
    u_low = upper_map(Interval.point(p.low))
    u_high = upper_map(Interval.point(p.high))
    left_sign = lower_map(u_low) - p.low
    right_sign = lower_map(u_high) - p.high
    _require(left_sign.low > 0, "F(p_lower)-p_lower is not strictly positive")
    _require(right_sign.high < 0, "F(p_upper)-p_upper is not strictly negative")
    # u is strictly decreasing on J. Its endpoint evaluations enclose q.
    q = Interval(u_high.low, u_low.high)
    _require(p.high < q.low, "q > p is not certified")
    width = (q - p) / g
    _require(0 < width.low and width.high < 1,
             "the continuous inverse limiting width is not in (0,1)")

    # Exact arithmetic behind the self-map endpoint bounds.
    e2g = Fraction(27, 16)
    log_argument = (3 * e2g - 1) / 2
    _require(log_argument == Fraction(65, 32),
             "the exact u(b-g) logarithm argument identity failed")
    _require(e2g < log_argument < e2g * e2g,
             "the exact self-map endpoint comparisons failed")
    ell_left = b - g + slope * g
    u_left = b - 2 * g + log_interval(log_argument) / 2
    gaps = {
        "ell_at_left_minus_left": slope * g,
        "right_minus_ell_at_left": (1 - slope) * g,
        "u_at_left_minus_left": log_interval(log_argument) / 2 - g,
        "right_minus_u_at_left": 2 * g - log_interval(log_argument) / 2,
    }
    for name, value in gaps.items():
        _require(value.low > 0, "self-map endpoint gap is not positive: " + name)

    values = {
        "log2": log2, "log3": log3, "g": g, "alpha": alpha,
        "b": b, "theta": theta, "slope_magnitude": slope,
        "contraction": contraction, "J_lower": j_low, "J_upper": j_high,
        "p": p, "q": q, "width": width,
        "F_at_p_lower_minus_p_lower": left_sign,
        "F_at_p_upper_minus_p_upper": right_sign,
        "u_at_p_lower": u_low, "u_at_p_upper": u_high,
        "ell_at_J_lower": ell_left, "u_at_J_lower": u_left,
        "ell_and_u_at_J_upper": j_low,
        "u_derivative_absolute_range": Interval(Fraction(16, 65), Fraction(1, 2)),
    }
    values.update(gaps)
    return values


def verify_intervals(data):
    """Verify decimal brackets and return a JSON-ready rational certificate.

    Required keys: p, q, width. Optional keys: g, alpha, b, theta,
    contraction. Each value is [lower_decimal_string, upper_decimal_string].
    Supplied p endpoints are tested by strict opposite signs of F(x)-x.
    Every other supplied decimal interval must strictly contain the newly
    computed closed rational enclosure. Unknown keys are rejected here too.
    """
    _require(type(data) is dict, "interval displays must be an object")
    keys = frozenset(data)
    _require(_REQUIRED <= keys, "missing required p, q, or width display")
    _require(keys <= _REQUIRED | _OPTIONAL, "unknown interval display field")
    displays = {name: _parse_display(name, pair) for name, pair in data.items()}
    _require(displays["q"].low > displays["p"].high,
             "displayed q interval is not strictly above displayed p interval")
    _require(0 < displays["width"].low and displays["width"].high < 1,
             "displayed width interval must lie strictly in (0,1)")
    values = _compute(displays["p"])
    for name, display in displays.items():
        if name != "p":
            _strictly_inside(name, values[name], display)
    return {
        "status": "PASS",
        "arithmetic": "integer and Fraction arithmetic only; no binary floating point",
        "method": {
            "outward_rational_grid_denominator": str(SCALE),
            "logarithm_terms": LOG_TERMS,
            "logarithm_range_reduction": "1 <= x <= 2; atanh argument in [0,1/3]",
            "logarithm_tail_upper": _rational_text(Fraction(
                9, 4 * (2 * LOG_TERMS + 1) * 3 ** (2 * LOG_TERMS + 1))),
            "exponential_terms": EXP_TERMS,
            "exponential_range_reduction": "0 <= x <= 1/8; negative inputs by reciprocal",
            "exponential_tail": "first omitted term / (1-x/(N+2)); then repeated squaring",
        },
        "verified_displays": {name: list(pair) for name, pair in data.items()},
        "intervals": {name: _record(value) for name, value in values.items()},
        "checks": {
            "positive_g": True,
            "theta_strictly_between_half_and_one": True,
            "p_bracket_inside_J": True,
            "F_left_sign_strictly_positive": True,
            "F_right_sign_strictly_negative": True,
            "q_strictly_above_p": True,
            "limiting_inverse_width_strictly_below_one": True,
            "contraction_strictly_below_one": True,
            "self_map_endpoint_gaps_strictly_positive": True,
            "all_supplied_decimal_enclosures_verified": True,
        },
        "exact_endpoint_arithmetic": {
            "exp_2g": "27/16",
            "u_left_log_argument": "65/32",
            "lower_comparison_gap": _rational_text(Fraction(65, 32) - Fraction(27, 16)),
            "upper_comparison_gap": _rational_text(Fraction(27, 16) ** 2 - Fraction(65, 32)),
            "u_derivative_absolute_bounds": ["16/65", "1/2"],
            "endpoint_identity": "ell(b)=u(b)=b-g",
        },
    }


def generate_certificate():
    """Return the certificate with default display brackets and suggestions."""
    certificate = verify_intervals(DEFAULT_DISPLAYS)
    suggestions = {name: list(pair) for name, pair in DEFAULT_DISPLAYS.items()}
    for name in sorted(_OPTIONAL):
        exact = certificate["intervals"][name]["rational"]
        suggestions[name] = [
            _decimal_bound(Fraction(exact[0]), 40, False),
            _decimal_bound(Fraction(exact[1]), 40, True),
        ]
    # Recheck the generated suggestions as rigorously as supplied inputs.
    verify_intervals(suggestions)
    certificate["suggested_displays"] = suggestions
    return certificate


if __name__ == "__main__":
    print(json.dumps(generate_certificate(), indent=2, sort_keys=True))
