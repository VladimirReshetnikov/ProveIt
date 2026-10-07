#!/usr/bin/env python3
"""Regenerate authoritative integer/Fraction checks and all terms through 1500."""
from __future__ import annotations
import argparse
from fractions import Fraction as Q
import hashlib
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True
ROOT = Path(__file__).absolute().parents[1]
sys.path.insert(0, str(ROOT / 'code'))
sys.path.insert(0, str(ROOT))
import partition_exact
import verify_manifest as manifest


def need(condition, message):
    if not condition:
        raise ValueError(message)


def canonical(value):
    return (json.dumps(value, sort_keys=True, indent=2, allow_nan=False) + '\n').encode()


def sign_certificate():
    # log(3/2) = 2*atanh(1/5). Bound all denominators in the k>=2
    # tail below by 5 and sum the resulting geometric series.
    upper = Q(2,5) + Q(2,375) + Q(1,7500)
    rational_bound = Q(811,2000)
    polynomial = lambda x: 26*x*x - 82*x + 29
    need(upper == Q(3041,7500) and upper < rational_bound < 1,
         'logarithm upper-bound calculation failed')
    need(polynomial(rational_bound) == Q(48373,2000000) > 0,
         'first-correction polynomial sign failed')
    need(52*rational_bound - 82 < 0, 'polynomial monotonicity failed')
    # S=Li2(2/3)-Li2(1/3)+log(3/2)*log(2)>0, since each
    # difference of the positive dilogarithm summands is positive.
    return {'log_3_over_2_strict_upper_bound': str(upper),
            'larger_rational_bound': str(rational_bound),
            'Q_at_larger_bound': str(polynomial(rational_bound)),
            'Q_definition': '26*x^2-82*x+29',
            'radial_correction': '-Q(a)/(144*(a-1)^2) < 0',
            'coefficient_correction': 'B*sqrt(S)-3/(16*sqrt(S)) < 0',
            'S_positive_reason': 'Li2(2/3)-Li2(1/3) has strictly positive termwise differences; a*log(2)>0',
            'arithmetic': 'exact Fraction comparisons; no decimal inference'}


def zero_certificate(values):
    degree = 1000
    need(len(values) >= degree + 2, 'not enough coefficients for zero certificate')
    rows = []
    for radius, b, target, direction in [(Q(3,4), 5, Q(1,4), 'greater'),
                                         (Q(4,5), 6, -Q(1,2), 'less')]:
        outer = Q(b-1,b)
        polynomial = Q(0)
        for n in range(degree, -1, -1):
            polynomial = polynomial * (-radius) + values[n+1]
        tail = (radius/outer)**(degree+1) * Q(b**b) / outer
        need(tail < Q(1,10**12), 'tail bound exceeds advertised tolerance')
        gap = polynomial - tail - target if direction == 'greater' else target - polynomial - tail
        need(gap > 0, 'rational sign certificate failed')
        rows.append({'q': str(-radius), 'comparison': direction, 'target': str(target),
                     'tail_upper_bound': str(tail), 'tail_less_than_1e_minus_12': True,
                     'strict_gap_positive': True,
                     'strict_gap_sha256': hashlib.sha256(str(gap).encode()).hexdigest()})
    return {'degree': degree, 'normalization': 'G(q)=F(q)/q', 'bounds': rows,
            'conclusion': 'G has a real zero in (-4/5,-3/4), excluding finite eta quotients after monomial normalization',
            'tail_majorant': '(r/R)^(N+1)*b^b/R, R=(b-1)/b; a(n)<=p(n)'}


def check_prefix(values, prefix):
    need(type(prefix) is dict and set(prefix) == {'sequence', 'url', 'observed_date', 'scope', 'offset', 'terms'},
         'OEIS prefix schema mismatch')
    need(prefix['sequence'] == 'A239950' and prefix['url'] == 'https://oeis.org/A239950'
         and prefix['observed_date'] == '2026-10-04' and type(prefix['offset']) is int and prefix['offset'] == 0
         and prefix['scope'] == '58 displayed terms; b-file not retrieved',
         'OEIS prefix metadata mismatch')
    terms = prefix['terms']
    need(type(terms) is list and len(terms) == 58
         and all(type(value) is int and value >= 0 for value in terms),
         'OEIS prefix must contain exactly 58 nonnegative integer terms')
    need(values[:58] == terms, 'observed OEIS prefix mismatch')


def verify(values, prefix):
    need(type(values) is list and len(values) == 1501
         and all(type(value) is int and value >= 0 for value in values),
         'count vector must contain 1501 nonnegative integers')
    check_prefix(values, prefix)
    for n in range(36):
        brute = sum(bool(parts) and parts[0] == len(set(parts))
                    for parts in partition_exact.partitions(n))
        need(brute == values[n], 'independent brute force mismatch at n=' + str(n))
    count = 200
    normalized = values[1:count+2]
    logarithmic, euler = [0]*(count+1), [0]*(count+1)
    for n in range(1,count+1):
        logarithmic[n] = n*normalized[n] - sum(logarithmic[j]*normalized[n-j] for j in range(1,n))
        numerator = logarithmic[n] - sum(d*euler[d] for d in range(1,n) if n % d == 0)
        need(numerator % n == 0, 'nonintegral Euler exponent')
        euler[n] = numerator // n
    periods = [p for p in range(1,51) if all(euler[n] == euler[n-p] for n in range(p+1,count+1))]
    need(periods == [], 'unexpected small pure period in Euler exponents')
    return {'status': 'PASS', 'arithmetic': 'integer and Fraction only',
            'sequence': 'A239950', 'maximum_n': 1500,
            'observed_OEIS_terms_checked': 58, 'brute_force_maximum_n': 35,
            'independent_brute_force_cases': 36,
            'euler_exponents_1_through_200': euler[1:],
            'pure_periods_1_through_50_matching_through_200': periods,
            'first_correction_sign': sign_certificate(),
            'interior_zero': zero_certificate(values),
            'scope': 'Finite exact checks and rational sign certificates; asymptotic transfer is proved in Report195.tex'}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output-dir', type=Path, required=True)
    args = parser.parse_args()
    try:
        output = manifest.fresh_output(args.output_dir, ROOT)
        prefix = manifest.load_json(manifest.read_regular(ROOT / 'data/oeis_prefix.json'))
        values = partition_exact.counts(1500)
        result = verify(values, prefix)
        terms = ''.join(str(n)+' '+str(value)+'\n' for n,value in enumerate(values)).encode()
        result['exact_terms_sha256'] = hashlib.sha256(terms).hexdigest()
        result['exact_terms_bytes'] = len(terms)
        output.mkdir(exist_ok=False)
        for name, payload in [('exact_terms.txt', terms), ('exact_checks.json', canonical(result))]:
            with (output/name).open('xb') as stream:
                stream.write(payload)
        sys.stdout.buffer.write(canonical(result))
    except (ValueError, OSError, TypeError) as exc:
        print(json.dumps({'status':'FAIL','error':str(exc)},sort_keys=True),file=sys.stderr)
        return 1
    return 0


if __name__ == '__main__':
    sys.exit(main())
