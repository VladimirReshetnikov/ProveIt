#!/usr/bin/env python3
"""Bounded, exact, stdout-only companion to Report164.

No third-party dependencies, network access, application file reads/writes, or
work at import time. Use Python's -B switch to suppress interpreter bytecode.
The public API is given by __all__; all indexed entry points validate before
coefficient allocation. Verification failures remain active under Python -O.
"""

from argparse import ArgumentParser, ArgumentTypeError
from fractions import Fraction as _F
from itertools import permutations as _permutations
from math import factorial as _factorial, isqrt as _isqrt
import json as _json
import sys as _sys

__all__ = [
    "MAX_COUNT_N", "MAX_VERIFY_N", "VerificationError", "count_coefficients",
    "quotient_coefficients", "verify", "certify_constants",
    "resultant_nonzero_check", "main",
]
MAX_COUNT_N = 400
MAX_VERIFY_N = 70


class VerificationError(ValueError):
    """An explicit exact-arithmetic consistency or enclosure check failed."""


def _require(condition, message):
    if not condition:
        raise VerificationError(message)


def _validate_n(n, maximum):
    # Reject booleans, floats, strings, integer-like objects, and subclasses.
    # Do not format an unbounded integer into an error message.
    if type(n) is not int:
        raise TypeError("n must be an int, excluding bool")
    if not 0 <= n <= maximum:
        raise ValueError("n must satisfy 0 <= n <= " + str(maximum))
    return n


def _binomial_row(n):
    """Yield a row without storing a Pascal triangle or even an entire row."""
    value = 1
    for k in range(n + 1):
        yield value
        if k < n:
            value = value * (n - k) // (k + 1)


def count_coefficients(n):
    """Return integer p_0,...,p_n for 0 <= n <= 400.

    Four binomial sums from the Riccati equation use O(n^2) arithmetic
    operations and O(n) stored scalar entries. This is not a bit-cost bound.
    """
    n = _validate_n(n, MAX_COUNT_N)
    p = [1]
    squares = []
    weighted_squares = []
    for degree in range(n):
        e_sum = 0
        square_sum = 0
        g_sum = 0
        for k, choose in enumerate(_binomial_row(degree)):
            e_sum += choose * p[k]
            square_sum += choose * p[k] * p[degree - k]
            if k < degree:
                g_sum += choose * p[k + 1]
        squares.append(square_sum)
        t_sum = 0
        power_two = 1 << degree
        for k, choose in enumerate(_binomial_row(degree)):
            t_sum += choose * power_two * squares[k]
            power_two //= 2
        weighted_squares.append(t_sum)
        q_now = 3 if degree == 0 else 4
        q_previous = 0 if degree == 0 else 3 if degree == 1 else 4
        numerator = (
            2 * p[degree] - 4 * e_sum + 2 * q_now + degree * q_previous
            + 2 * t_sum - 8 * g_sum
        )
        if degree:
            numerator += degree * weighted_squares[degree - 1]
        quotient, remainder = divmod(numerator, 6)
        _require(remainder == 0, "Riccati numerator is not divisible by six")
        p.append(quotient)
    return p


def _series_multiply(a, b, n):
    result = [_F(0)] * (n + 1)
    for i, ai in enumerate(a):
        if ai:
            for j in range(min(len(b), n + 1 - i)):
                if b[j]:
                    result[i + j] += ai * b[j]
    return result


def _exponential_series(rate, n):
    result = [_F(1)]
    for k in range(1, n + 1):
        result.append(result[-1] * rate / k)
    return result


def _quotient_series(n):
    """Independent ordinary power series; never calls the Riccati route."""
    zero = [_F(0)] * (n + 1)
    one = zero.copy()
    one[0] = _F(1)
    exp_half = _exponential_series(_F(1, 2), n)
    q = [4 * v for v in _exponential_series(_F(1), n)]
    q[0] -= 1
    h = zero.copy()
    j = zero.copy()
    q_power = one
    for k in range(n // 2 + 1):
        h_factor = _F((-1) ** k, 16 ** k * _factorial(2 * k))
        for i in range(n + 1 - 2 * k):
            h[i + 2 * k] += h_factor * q_power[i]
        if 2 * k + 1 <= n:
            j_factor = _F((-1) ** k, 4 * 16 ** k * _factorial(2 * k + 1))
            for i in range(n - 2 * k):
                j[i + 2 * k + 1] += j_factor * q_power[i]
        if k < n // 2:
            q_power = _series_multiply(q_power, q, n)
    b = [2 * v for v in exp_half]
    b[0] += 1
    bj = _series_multiply(b, j, n)
    inner = [hi + bji for hi, bji in zip(h, bj)]
    numerator = _series_multiply(
        _exponential_series(_F(-1), n), _series_multiply(q, inner, n), n
    )
    bh = _series_multiply(b, h, n)
    qj = _series_multiply(q, j, n)
    denominator = [x - y for x, y in zip(bh, qj)]
    _require(denominator[0] == 3, "Unexpected quotient denominator at zero")
    result = zero.copy()
    for degree in range(n + 1):
        convolution = sum(
            (denominator[k] * result[degree - k] for k in range(1, degree + 1)),
            _F(0),
        )
        result[degree] = (numerator[degree] - convolution) / denominator[0]
    return result


def quotient_coefficients(n):
    """Return p_0,...,p_n from the independent Fraction quotient, n <= 70."""
    n = _validate_n(n, MAX_VERIFY_N)
    coefficients = _quotient_series(n)
    counts = []
    factorial = 1
    for degree, value in enumerate(coefficients):
        if degree:
            factorial *= degree
        integer = value * factorial
        _require(integer.denominator == 1, "A quotient-derived count is not integral")
        counts.append(integer.numerator)
    return counts


# FROZEN_FIXTURE_START
# Preparation-time source hash; no runtime file I/O.
_SOURCE_SHA256 = 'd42dae1bbac32f2b952b3ccbeea48c3d90505204fe513ecea9556ae0bcb27d4a'
_SOURCE_COUNTS = (
    1,
    1,
    1,
    3,
    11,
    49,
    263,
    1653,
    11877,
    95991,
    862047,
    8516221,
    91782159,
    1071601285,
    13473914281,
    181517350571,
    2608383775171,
    39824825088809,
    643813226048935,
    10986188094959045,
    197337931571468445,
    3721889002400665951,
    73539326922210382215,
    1519081379788242418149,
    32743555520207058219615,
    735189675389014372317381,
    17167470189102029106503457,
    416297325393961581614919699,
    10468759109047048511785181499,
    272663345523662949571086535201,
    7346518362495550669587951987399,
    204539324291355079758576427320853,
    5878416448467628215599958670190869,
    174223945386975482728912851110751431,
    5320106374135453888563313157982976111,
    167232974698164950641578719412434688845,
    5407019929661274797886581276653666104943,
    179677314965899717327756420597568210468933,
    6132116544121046402686046213590718114272089,
    214787281796488809444762543177377466419782267,
    7716175695131570964771559074490172330993576115,
    284131588386675257705011846785657928372695002841,
    10717718945463416620327720805595647805635809236711,
    413908527884993695909526722330319436067536797304549,
    16356508568742954048255540186930772843919017766669517,
    661053598808034620660440013405109251647269697650963759,
    27310399945864015416169259367335991197188107439119836055,
    1152814612512135724390948173365326528383283551264264024373,
    49697468228050973738649005317690532376929579854198986773439,
    2187076123517407341996190590846832934405779052572657249181317,
    98212656532414913602577958678041386154811465461169048198199633,
    4498535883329932156938414166454851676826073833705490517513319395,
    210091309146376988745316244105054446800630473783319781125596146603,
    10000403225838039297514139858411182720933357784475021988947158342609,
    485003447833960912539525493394455653395222499938205843713524736519047,
    23957476458935958381934654086799125239914218029211184160291029132187573,
    1204932314577163679063298965773124467136538026614936112900148294675205317,
    61683791708767837423538279563794038738914953102729344399407484920095180439,
    3213161910981807664806220231399122306908172852376668835979685617427232653951,
    170262174795153337471320056808265527720640999531071492009222910538377171734045,
    9174934688633553795432950931693456554803479979054393637477153063312491070520783,
    502650791850876324352341623677183713917073473780666057703867545379246086982528261,
    27989272808455328715771720958047873666014311207910120937494438543442429791610642441,
    1583673753870060701528675315324212377032481982028615173425275476728888875991300143691,
    91028890175785060999779477516804113789124148008869593149490419975859350457132314133923,
    5314056396115734822605781367787426423531291755198274475162095534294923270903991174728585,
    314994992089174614248499003306922793650148455089223818715929856460332924883982846842264103,
    18954485767856613974140213711411042554108823397013301334847192492609704965176419339399567365,
    1157589220334714728270401728246121993789341257501409594736332355510396139738540028979712901629,
    71735993807536581251893056394592050518340604128745080449955598738666437329898219667752418794751,
    4509918709779623767450744053714823629593899853380943076380113423948190149807924015710118751513767,
)
# FROZEN_FIXTURE_END


def resultant_nonzero_check():
    """Independently evaluate the 4-by-4 Sylvester determinant at one jet."""
    # At (z,p,u,v)=(0,1,0,0), F=2 X^2+4 X and G=5 X^2+8 X-1.
    z, p, u, v = 0, 1, 0, 0
    a = (z + 2) * p * p
    b = -8 * u - 4 * p + 4 * (z + 2)
    c = 2 * u + 2 * p - (z + 2)
    a2 = p * p + 2 * (z + 2) * p * u + 2 * a
    b2 = -8 * v - 4 * u + 4 + b
    c2 = 2 * v + 2 * u - 1
    matrix = ((a, b, c, 0), (0, a, b, c),
              (a2, b2, c2, 0), (0, a2, b2, c2))
    determinant = 0
    for permutation in _permutations(range(4)):
        inversions = sum(permutation[i] > permutation[j]
                         for i in range(4) for j in range(i + 1, 4))
        term = -1 if inversions % 2 else 1
        for row, column in enumerate(permutation):
            term *= matrix[row][column]
        determinant += term
    _require(determinant == -12, "Resultant specialization is not -12")
    return {
        "jet_z_p_u_v": [z, p, u, v],
        "quadratics_descending_coefficients": [[a, b, c], [a2, b2, c2]],
        "sylvester_determinant": determinant,
        "nonzero_annihilator_specialization_verified": True,
    }


def verify(n=MAX_VERIFY_N):
    """Compare both independent routes with the embedded source fixture."""
    n = _validate_n(n, MAX_VERIFY_N)
    recurrence = count_coefficients(n)
    quotient = quotient_coefficients(n)
    fixture = list(_SOURCE_COUNTS[:n + 1])
    _require(recurrence == fixture, "Riccati counts do not match the source fixture")
    _require(quotient == fixture, "Quotient counts do not match the source fixture")
    _require(recurrence == quotient, "Independent coefficient routes disagree")
    return {
        "schema": 1,
        "report": "Report164",
        "sequence": "A307030",
        "verified_through_n": n,
        "counts_as_decimal_strings": [str(v) for v in recurrence],
        "checks": {
            "branch_free_quotient_matches_fixture": True,
            "riccati_recurrence_matches_fixture": True,
            "independent_routes_match": True,
            "riccati_divisibility_checks": n,
            "quotient_integrality_checks": n + 1,
        },
        "fixture_provenance": _fixture_provenance(),
        "resultant_check": resultant_nonzero_check(),
        "limitations": (
            "Finite exact coefficient checks and one resultant specialization. "
            "These checks do not prove the analytic theorems, a next-pole gap, "
            "or an effective asymptotic error bound."
        ),
    }


def _fixture_provenance():
    return {
        "source_artifact": "Report161/data/counts.json",
        "source_sha256": _SOURCE_SHA256,
        "source_method": "CGP endpoint recurrence (2), optimized by (4)-(5)",
        "posted_oeis_scope": "p_1 through p_25 only, as checked in Report161",
        "beyond_posted_oeis": "p_26 through p_70 are earlier endpoint-recurrence values",
        "empty_case": "p_0 = 1 by the empty-permutation convention",
        "oeis_url": "https://oeis.org/A307030",
        "counting_paper_url": "https://arxiv.org/abs/1908.08910",
    }


# Fixed proof parameters. All computations below use int or Fraction only.
_EXP_DEGREE = 200
_TRIG_LAST_INDEX = 60
_SQRT_PLACES = 120
_SQRT_SCALE = 10 ** _SQRT_PLACES
_RHO_LOWER = _F("1.11343904173672704376166152691808324014139016583344946615")
_RHO_UPPER = _F("1.11343904173672704376166152691808324014139016583344946616")
_C_LOWER = _F("0.695688549070635767995703168724110156574198350721")
_C_UPPER = _F("0.695688549070635767995703168724110156574198350722")


def _add(a, b):
    return (a[0] + b[0], a[1] + b[1])


def _sub(a, b):
    return (a[0] - b[1], a[1] - b[0])


def _mul(a, b):
    products = [x * y for x in a for y in b]
    return (min(products), max(products))


def _div(a, b):
    _require(0 < b[0] <= b[1], "Interval denominator must be positive")
    return _mul(a, (_F(1) / b[1], _F(1) / b[0]))


def _fixed(x):
    return (_F(x), _F(x))


def _exp_point(x):
    _require(0 <= x < _EXP_DEGREE + 2, "Exponential-tail hypothesis failed")
    term = _F(1)
    total = term
    for k in range(1, _EXP_DEGREE + 1):
        term *= x / k
        total += term
    next_term = term * x / (_EXP_DEGREE + 1)
    upper = total + next_term / (1 - x / (_EXP_DEGREE + 2))
    _require(total <= upper, "Exponential interval is reversed")
    return (total, upper)


def _exp_interval(x):
    return (_exp_point(x[0])[0], _exp_point(x[1])[1])


def _sqrt_point(x):
    _require(x >= 0, "Square-root argument is negative")
    square_scale = _SQRT_SCALE * _SQRT_SCALE
    k = _isqrt((x.numerator * square_scale) // x.denominator)
    _require(_F(k * k, square_scale) <= x < _F((k + 1) ** 2, square_scale),
             "Integer-square-root enclosure failed")
    return (_F(k, _SQRT_SCALE), _F(k + 1, _SQRT_SCALE))


def _sqrt_interval(x):
    return (_sqrt_point(x[0])[0], _sqrt_point(x[1])[1])


def _trig_point(x, sine):
    _require(0 <= x <= 1, "Alternating trigonometric bound requires 0 <= x <= 1")
    _require(_TRIG_LAST_INDEX % 2 == 0, "Trigonometric last index must be even")
    term = x if sine else _F(1)
    total = term
    for k in range(1, _TRIG_LAST_INDEX + 1):
        a = 2 * k if sine else 2 * k - 1
        term *= -x * x / (a * (a + 1))
        total += term
    a = 2 * (_TRIG_LAST_INDEX + 1) if sine else 2 * (_TRIG_LAST_INDEX + 1) - 1
    next_magnitude = term * x * x / (a * (a + 1))
    _require(next_magnitude >= 0, "Trigonometric tail must be nonnegative")
    return (total - next_magnitude, total)


def _sin_interval(x):
    return (_trig_point(x[0], True)[0], _trig_point(x[1], True)[1])


def _cos_interval(x):
    return (_trig_point(x[1], False)[0], _trig_point(x[0], False)[1])


def _denominator(x):
    exp_half = _exp_interval(_div(x, _fixed(2)))
    q = _sub(_mul(_fixed(4), _exp_interval(x)), _fixed(1))
    r = _sqrt_interval(q)
    angle = _div(_mul(x, r), _fixed(4))
    _require(0 < angle[0] <= angle[1] < 1, "Pole-bracket angle is not in (0,1)")
    value = _sub(
        _mul(_add(_mul(_fixed(2), exp_half), _fixed(1)), _cos_interval(angle)),
        _mul(r, _sin_interval(angle)),
    )
    return value, angle


def _decimal_floor(x, places):
    scale = 10 ** places
    integer = x.numerator * scale // x.denominator
    sign = "-" if integer < 0 else ""
    integer = abs(integer)
    return sign + str(integer // scale) + "." + str(integer % scale).zfill(places)


def _decimal_ceil(x, places):
    scale = 10 ** places
    integer = -((-x.numerator * scale) // x.denominator)
    return _decimal_floor(_F(integer, scale), places)


def _outward_decimal(interval, places):
    lower = _decimal_floor(interval[0], places)
    upper = _decimal_ceil(interval[1], places)
    _require(_F(lower) <= interval[0] <= interval[1] <= _F(upper),
             "Outward decimal rounding check failed")
    return [lower, upper]


def certify_constants():
    """Return an exact rational rho/C certificate; takes no external input.

    Monotonicity and first-pole identification are proved in Report164. This
    computation checks all the finite inequalities used by that argument.
    """
    _require(0 < _RHO_LOWER < _RHO_UPPER, "Invalid positive rho bracket")
    lower_value, lower_angle = _denominator(_fixed(_RHO_LOWER))
    upper_value, upper_angle = _denominator(_fixed(_RHO_UPPER))
    _require(lower_value[0] > 0, "D(rho_lower) is not certified positive")
    _require(upper_value[1] < 0, "D(rho_upper) is not certified negative")
    rho = (_RHO_LOWER, _RHO_UPPER)
    exp_rho = _exp_interval(rho)
    q = _sub(_mul(_fixed(4), exp_rho), _fixed(1))
    amplitude = _div(
        _mul(_fixed(2), q),
        _mul(_mul(exp_rho, exp_rho), _mul(rho, _add(rho, _fixed(2)))),
    )
    _require(0 < _C_LOWER < amplitude[0] <= amplitude[1] < _C_UPPER,
             "Propagated amplitude is not inside the claimed strict C bracket")
    return {
        "schema": 1,
        "report": "Report164",
        "method": "Exact Fraction intervals, Taylor bounds, and integer square root",
        "parameters": {
            "exp_taylor_degree": _EXP_DEGREE,
            "trig_last_index": _TRIG_LAST_INDEX,
            "sqrt_lattice_decimal_places": _SQRT_PLACES,
        },
        "rho_rational_bracket": [str(v) for v in rho],
        "rho_decimal_bracket": _outward_decimal(rho, 56),
        "D_at_rho_lower": _outward_decimal(lower_value, 80),
        "D_at_rho_upper": _outward_decimal(upper_value, 80),
        "angle_at_rho_lower": _outward_decimal(lower_angle, 60),
        "angle_at_rho_upper": _outward_decimal(upper_angle, 60),
        "amplitude_propagated_interval": _outward_decimal(amplitude, 60),
        "C_rational_bracket": [str(_C_LOWER), str(_C_UPPER)],
        "C_decimal_bracket": _outward_decimal((_C_LOWER, _C_UPPER), 48),
        "checks": {
            "exact_taylor_and_square_root_hypotheses": True,
            "trigonometric_arguments_in_zero_one": True,
            "D_at_lower_strictly_positive": True,
            "D_at_upper_strictly_negative": True,
            "propagated_C_strictly_inside_claimed_bracket": True,
            "outward_decimal_rounding_verified": True,
            "all_exact_inequalities_verified": True,
        },
        "limitations": (
            "The proof of phase monotonicity and identification with the first "
            "positive pole is in Report164. This certificate does not locate "
            "nonreal poles, certify a next-pole modulus, or give an effective "
            "coefficient-error constant or onset."
        ),
    }


def _cli_n(text, maximum):
    # Bound the textual representation before any conversion or allocation.
    digits = text[1:] if text.startswith("+") else text
    if not digits or len(digits) > len(str(maximum)) or not all("0" <= c <= "9" for c in digits):
        raise ArgumentTypeError("n must be an integer between 0 and " + str(maximum))
    value = int(digits)
    if value > maximum:
        raise ArgumentTypeError("n must be an integer between 0 and " + str(maximum))
    return value


def main(argv=None):
    """CLI entry point; emit one JSON object to stdout, errors to stderr."""
    parser = ArgumentParser(description=__doc__)
    commands = parser.add_subparsers(dest="command", required=True)
    counts_parser = commands.add_parser("counts", help="Riccati counts, 0 <= n <= 400")
    counts_parser.add_argument("--n", required=True, type=lambda text: _cli_n(text, MAX_COUNT_N))
    verify_parser = commands.add_parser("verify", help="Independent quotient check, 0 <= n <= 70")
    verify_parser.add_argument("--n", default=MAX_VERIFY_N, type=lambda text: _cli_n(text, MAX_VERIFY_N))
    commands.add_parser("certify", help="Exact rational rho/C interval certificate")
    args = parser.parse_args(argv)
    try:
        if args.command == "counts":
            result = {
                "schema": 1,
                "report": "Report164",
                "sequence": "A307030",
                "max_n": args.n,
                "method": "Exact integer Riccati recurrence",
                "arithmetic_complexity": "O(N^2) arithmetic operations; O(N) scalar storage",
                "bit_complexity_claim": False,
                "counts_as_decimal_strings": [str(v) for v in count_coefficients(args.n)],
            }
        elif args.command == "verify":
            result = verify(args.n)
        else:
            result = certify_constants()
    except (TypeError, ValueError, ArithmeticError) as error:
        parser.exit(2, "error: " + str(error) + "\n")
    print(_json.dumps(result, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
