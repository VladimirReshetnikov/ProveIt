#!/usr/bin/env python3
"""Mandatory exact finite checks for Report185; Python standard library only.

No floating-point computation, network access, or assertion-dependent guard is
used. These checks do not replace the report's analytic proof of its theorem.
"""
from __future__ import annotations
import argparse
from fractions import Fraction as Q
import hashlib
import json
import math
from pathlib import Path
import sys
sys.dont_write_bytecode = True
ROOT = Path(__file__).absolute().parent.parent
sys.path.insert(0, str(ROOT))
import verify_manifest as manifest

FIXTURE = [0,1,2,13,71,558,5344,60926,766898,10759096,168848256,
           2947203048,56368708824,1165246323408,25802649445728,
           609940593443952,15377212949988624,412827548455415040,
           11764577341464710016,354392697960438122880,
           11237993013428254071936]
EXACT_MAX_N = 600
FINITE_MAX_N = 60
Q_IDENTITY_MAX_N = 100

def require(condition, message):
    if not condition:
        raise ArithmeticError(message)


def odd_sigma(k):
    require(type(k) is int and k >= 1, 'odd_sigma needs a positive integer')
    return sum(d for d in range(1, k + 1, 2) if k % d == 0)


def direct_q(k):
    """[q^k] sum_j log(1+q^j), from the alternating logarithm series."""
    return sum((Q((-1) ** (r + 1), r) for r in range(1, k + 1)
                if k % r == 0), Q(0))


def exact_values(N):
    """Unsigned-Stirling recurrence followed by the integer weight transform."""
    require(type(N) is int and N >= 0, 'N must be a nonnegative integer')
    weights = [0] + [math.factorial(k - 1) * odd_sigma(k) for k in range(1, N + 1)]
    row, values = [1], [0]
    for n in range(1, N + 1):
        row = [0] + [row[k - 1] + (n - 1) * (row[k] if k < len(row) else 0)
                     for k in range(1, n + 1)]
        require(sum(row) == math.factorial(n), 'Stirling row-sum failure at ' + str(n))
        val = sum(row[k] * weights[k] for k in range(1, n + 1))
        require(val > 0, 'positivity failure at ' + str(n))
        if n > 1:
            require(val > (n - 1) * values[-1], 'strict monotonicity failure at ' + str(n))
        values.append(val)
    return values


def multiply(a, b, N):
    out = [Q(0)] * (N + 1)
    for i, x in enumerate(a):
        if x:
            for j, y in enumerate(b[:N + 1 - i]):
                if y:
                    out[i + j] += x * y
    return out


def composed_coefficients(B, N, coefficient=direct_q):
    """Direct truncated rational polynomial composition, with no Stirling rows."""
    require(len(B) == N + 1 and B[0] == 0, 'invalid polynomial decoration')
    result = [Q(0)] * (N + 1)
    power = [Q(1)] + [Q(0)] * N
    for k in range(1, N + 1):
        power = multiply(power, B, N)
        ck = coefficient(k)
        for n in range(1, N + 1):
            result[n] += ck * power[n]
    return result


def check_fixture(path, values):
    data = manifest.load_json(manifest.read_regular(path).decode('utf-8'))
    require(isinstance(data, dict) and set(data) == {'sequence', 'offset', 'values'},
            'invalid fixture schema')
    require(data['sequence'] == 'A330499' and type(data['offset']) is int and data['offset'] == 0,
            'invalid fixture sequence or offset')
    require(isinstance(data['values'], list) and len(data['values']) == 21 and
            all(type(x) is int and x >= 0 for x in data['values']), 'invalid fixture values')
    require(data['values'] == FIXTURE, 'frozen OEIS fixture differs')
    require(values[:21] == data['values'], 'Stirling transform differs from OEIS fixture')


def check_values(values, limit=EXACT_MAX_N):
    require(isinstance(values, list) and len(values) == limit + 1,
            'invalid exact-value count')
    require(all(type(x) is int for x in values), 'noninteger exact value')
    require(values[:21] == FIXTURE, 'exact prefix mismatch')
    for n in range(1, limit + 1):
        require(values[n] > 0, 'nonpositive exact value')
        if n > 1:
            require(values[n] > (n - 1) * values[n - 1], 'exact monotonicity mismatch')


def rational_tail_certificate(e_upper=None, pi_lower=Q(157, 50), exponent=Q(573, 100),
                              r=Q(1, 300), tail_limit=Q(1, 50)):
    # The external mathematical input pi>223/71 is Archimedes' classical bound.
    # Rational comparisons below are exact. Their analytic use as e/exponential
    # and harmonic-tail bounds is justified in the report, not by finite tests.
    standard_e_upper = sum((Q(1, math.factorial(k)) for k in range(10)), Q(0)) + Q(1, 9 * math.factorial(9))
    if e_upper is None:
        e_upper = standard_e_upper
    require(e_upper == standard_e_upper and e_upper < Q(87, 32), 'invalid rational e upper bound')
    alternate_e_upper = sum((Q(1, math.factorial(k)) for k in range(7)), Q(0)) + Q(1, math.factorial(7)) / (1 - Q(1, 8))
    require(alternate_e_upper == Q(31967, 11760) and alternate_e_upper < Q(87, 32),
            'alternate rational e upper bound failed')
    require(Q(223, 71) > pi_lower == Q(157, 50), 'invalid Archimedean simplification')
    require(pi_lower ** 2 / Q(55, 32) > exponent == Q(573, 100), 'invalid exponent lower bound')
    expsum = sum((exponent ** k / math.factorial(k) for k in range(21)), Q(0))
    require(expsum > 300, 'positive exponential Taylor sum failed')
    require(r == Q(1, 300), 'invalid geometric majorant ratio')
    tail = (1 + r) / (1 - r) ** 3 - 1
    require(tail == Q(359101, 26730899) and tail < tail_limit == Q(1, 50),
            'harmonic tail comparison failed')
    return {'e_upper': str(e_upper), 'alternate_e_upper': str(alternate_e_upper),
            'pi_input': 'Archimedes: pi > 223/71 (a theorem input, not a computed decimal)',
            'pi_rational_lower': str(pi_lower), 'exponent_lower': str(exponent),
            'exponential_taylor_degree': 20, 'taylor_sum_exceeds': 300,
            'ratio_upper': str(r), 'tail_bound': str(tail), 'tail_less_than': str(tail_limit)}


def run(fixture=ROOT / 'data/fixture21.json'):
    values = exact_values(EXACT_MAX_N)
    check_values(values)
    check_fixture(fixture, values)
    for k in range(1, Q_IDENTITY_MAX_N + 1):
        require(direct_q(k) == Q(odd_sigma(k), k), 'alternating-log identity failure at ' + str(k))
    N = FINITE_MAX_N
    L = [Q(0)] + [Q(1, n) for n in range(1, N + 1)]
    direct = composed_coefficients(L, N)
    for n in range(N + 1):
        require(direct[n] * math.factorial(n) == values[n],
                'direct rational log-decoration mismatch at ' + str(n))
    # Independent decoration: polynomial convolution vs closed finite binomial sum.
    B = [Q(0)] * (N + 1)
    B[1] = B[2] = Q(1, 2)
    two_point = composed_coefficients(B, N)
    for n in range(1, N + 1):
        finite = sum((Q(odd_sigma(k), k) * Q(math.comb(k, n - k), 2 ** k)
                      for k in range((n + 1) // 2, n + 1)), Q(0))
        require(two_point[n] == finite, 'two-point coefficient mismatch at ' + str(n))
    tail = rational_tail_certificate()
    digest = hashlib.sha256(','.join(map(str, values)).encode('ascii')).hexdigest()
    return {'status': 'PASS', 'standard_library_only': True, 'exact_fixture_terms': 21,
            'exact_stirling_max_n': EXACT_MAX_N, 'strict_monotonicity_through': EXACT_MAX_N,
            'stirling_row_sum_identity_through': EXACT_MAX_N,
            'q_product_identity_through': Q_IDENTITY_MAX_N,
            'independent_log_composition_through': N, 'independent_two_point_composition_through': N,
            'rational_tail_certificate': tail, 'exact_values_sha256': digest,
            'assertions_required': False,
            'scope': 'Exact finite arithmetic checks. The infinite asymptotic theorem is proved in Report185; no finite tests certify it.'}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--fixture', type=Path, default=ROOT / 'data/fixture21.json')
    parser.add_argument('--output', type=Path, help='new output file; never overwritten')
    args = parser.parse_args()
    try:
        result = run(args.fixture)
        data = (json.dumps(result, sort_keys=True, indent=2, allow_nan=False) + '\n')
        if args.output is not None:
            with args.output.open('x', encoding='utf-8') as stream:
                stream.write(data)
        print(data, end='')
    except (ArithmeticError, ValueError, OSError, TypeError) as exc:
        print(json.dumps({'status': 'FAIL', 'error': str(exc)}, sort_keys=True), file=sys.stderr)
        return 1
    return 0

if __name__ == '__main__':
    sys.exit(main())
