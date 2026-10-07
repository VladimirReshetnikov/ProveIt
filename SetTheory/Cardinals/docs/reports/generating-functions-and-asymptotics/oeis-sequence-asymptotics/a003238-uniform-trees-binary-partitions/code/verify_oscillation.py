"""Exact endpoint algebra for the dyadic profile oscillation lower bound.

Run beside RADIAL_VALUE_CERTIFICATE.json and OPERATOR_VALUE_CERTIFICATE.json,
or pass --input-dir.  This checker assumes their analytic enclosures, including
0 <= T^4 H <= 14 T^4 1 and |B3| <= epsilon_b.  It neither regenerates those
inputs nor claims that conditional constant intervals are profile values.
Only integers and Fraction affect results; explicit guards survive python -O.
"""
from __future__ import annotations

import argparse
import copy
from fractions import Fraction as F
import json
from pathlib import Path
import re

DEN = 1 << 256
POINTS = ('9/2097152', '3/524288')
CLAIM = F('0.00001839189788')


class CertificationError(ValueError):
    pass


def require(condition, message):
    if not condition:
        raise CertificationError(message)


def interval(raw, label):
    require(isinstance(raw, list) and len(raw) == 2, 'two endpoints required: ' + label)
    require(all(isinstance(v, str) and re.fullmatch(r'-?(0|[1-9][0-9]*)', v)
                for v in raw), 'integer-string endpoints required: ' + label)
    lo, hi = (F(int(v), DEN) for v in raw)
    require(lo <= hi, 'reversed interval: ' + label)
    return lo, hi


def floor(q):
    return q.numerator // q.denominator


def ceil(q):
    return -((-q.numerator) // q.denominator)


def fixed_bounds(lo, hi):
    return [str(floor(DEN * lo)), str(ceil(DEN * hi))]


def display(q, places=40):
    require(q >= 0, 'negative display value')
    scale = 10 ** places

    def fmt(n):
        return str(n // scale) + '.' + str(n % scale).zfill(places)

    return [fmt(floor(q * scale)), fmt(ceil(q * scale))]


def rational(q):
    return {'numerator': str(q.numerator), 'denominator': str(q.denominator),
            'outward_decimal': display(q)}


def strict_claim(claim, bound):
    require(0 < claim < bound, 'strict lower-bound claim not certified')


def derive(radial, operator, claim=CLAIM):
    for receipt, expected in ((radial, 'RADIAL_VALUES_ENCLOSED'),
                              (operator, 'POSITIVE_OPERATOR_ENCLOSED')):
        require(receipt.get('status') == expected, 'unexpected receipt status')
        require(type(receipt.get('precision_bits')) is int and receipt['precision_bits'] == 256,
                'precision must be integer 256')
        require(isinstance(receipt.get('rows'), list) and len(receipt['rows']) == 2,
                'exactly two rows required')
        require(tuple(row.get('t') for row in receipt['rows']) == POINTS,
                'wrong test points or row order')
    require(type(radial.get('N')) is int and radial['N'] == 1 << 24, 'unexpected coefficient cutoff')
    conditional, ratios, rows = [], [], []
    for rr, oo in zip(radial['rows'], operator['rows']):
        require(0 < F(rr['t']) <= F(1, 1024), 'test point outside operator domain')
        require(type(rr.get('N')) is int and rr['N'] == radial['N'], 'row cutoff mismatch')
        h = interval(rr['H_integer_bounds'], 'H')
        require(0 < h[0] <= h[1] < 14, 'radial H bound failed')
        tr_raw = oo['Tr_integer_bounds']
        require(isinstance(tr_raw, list) and len(tr_raw) == 4, 'four operator powers required')
        tr = [interval(a, 'T power') for a in tr_raw]
        require(tr[0] == (F(1), F(1)), 'T^0 1 must be exact one')
        require(all(a[0] >= 0 for a in tr), 'operator positivity not certified')
        s = interval(oo['S3_integer_bounds'], 'S3')
        require(s[0] > 0, 'positive S3 not certified')
        rebuilt_s = (tr[0][0] - tr[1][1] + tr[2][0] - tr[3][1],
                     tr[0][1] - tr[1][0] + tr[2][1] - tr[3][0])
        require(s == rebuilt_s, 'S3 reconstruction mismatch')
        r4 = interval(oo['14T4_integer_bounds'], '14T4')
        eb = interval(oo['epsilon_b_integer_bounds'], 'epsilon_b')
        require(r4[0] >= 0 and eb[0] >= 0, 'nonnegative remainder bounds required')

        # X=(H+B3-T^4 H)/S3, so the numerator has this signed enclosure.
        numerator = (h[0] - r4[1] - eb[1], h[1] + eb[1])
        corners = [n / d for n in numerator for d in s]
        old_bounds = fixed_bounds(min(corners), max(corners))
        conditional.append(interval(old_bounds, 'conditional C interval'))
        u_upper = sum((a[1] for a in tr), F(0))
        r_upper = u_upper / s[0]
        require(r_upper >= 1, 'U3/S3 upper bound below one')
        ratios.append(r_upper)
        rows.append({'t': rr['t'], 'conditional_C_integer_bounds': old_bounds,
                     'U3_upper': rational(u_upper), 'S3_lower': rational(s[0]),
                     'R_upper': rational(r_upper)})

    gap = conditional[0][0] - conditional[1][1]
    require(gap > 0, 'positive interval-separation gap required')
    bound = 2 * gap / sum(ratios, F(0))
    strict_claim(claim, bound)
    short_g = F('0.0000184727302644825')
    short_rs = [F('1.004024051499'), F('1.004765947242')]
    require(gap > short_g, 'printed gap bound failed')
    require(all(exact < short for exact, short in zip(ratios, short_rs)), 'printed R bound failed')
    short_bound = 2 * short_g / sum(short_rs, F(0))
    strict_claim(claim, short_bound)
    return {'status': 'PROFILE_OSCILLATION_LOWER_BOUND_VERIFIED', 'precision_bits': 256,
            'scope': 'Endpoint algebra conditional on the two analytic enclosure receipts. Actual profile oscillation, not pointwise profile values.',
            'rows': rows, 'gap_lower': rational(gap),
            'R_upper_sum': rational(sum(ratios, F(0))), 'weak_lower_bound': rational(bound),
            'strict_lower_bound': str(claim), 'strict_decimal_lower_bound': display(claim, 14)[0],
            'printed_certificate': {'gap_strict_lower': str(short_g),
                                    'R_strict_uppers': [str(q) for q in short_rs],
                                    'oscillation_strict_lower': str(short_bound),
                                    'positive_cross_multiplication_margin': str(2 * short_g - claim * sum(short_rs, F(0)))}}


def negative_probes(radial, operator):
    results = []

    def rejected(name, operation, expected):
        try:
            operation()
        except CertificationError as error:
            require(expected in str(error), 'wrong rejection for probe: ' + name)
            results.append({'probe': name, 'status': 'REJECTED', 'guard': str(error)})
        else:
            raise CertificationError('negative probe accepted: ' + name)

    def mutate(name, change, expected):
        pair = copy.deepcopy([radial, operator])
        change(pair)
        rejected(name, lambda: derive(*pair), expected)

    mutate('wrong status', lambda x: x[0].update(status='UNVERIFIED'), 'unexpected receipt status')
    mutate('float precision', lambda x: x[1].update(precision_bits=256.0), 'precision must be integer 256')
    mutate('wrong precision', lambda x: x[0].update(precision_bits=128), 'precision must be integer 256')
    mutate('missing row', lambda x: x[0]['rows'].pop(), 'exactly two rows required')
    mutate('wrong row order', lambda x: x[1]['rows'].reverse(), 'wrong test points or row order')
    mutate('row cutoff mismatch', lambda x: x[0]['rows'][0].update(N=1), 'row cutoff mismatch')
    mutate('noninteger endpoint', lambda x: x[0]['rows'][0]['H_integer_bounds'].__setitem__(0, '1.5'),
           'integer-string endpoints required')
    mutate('reversed H', lambda x: x[0]['rows'][0]['H_integer_bounds'].reverse(), 'reversed interval: H')
    mutate('false T^0', lambda x: x[1]['rows'][0]['Tr_integer_bounds'].__setitem__(0, ['0', '0']),
           'T^0 1 must be exact one')
    mutate('negative operator', lambda x: x[1]['rows'][0]['Tr_integer_bounds'].__setitem__(1, ['-1', '0']),
           'operator positivity not certified')
    mutate('zero S lower', lambda x: x[1]['rows'][0].update(S3_integer_bounds=['0', '1']),
           'positive S3 not certified')
    mutate('wrong S algebra', lambda x: x[1]['rows'][0]['S3_integer_bounds'].__setitem__(0, '1'),
           'S3 reconstruction mismatch')
    mutate('negative remainder', lambda x: x[1]['rows'][0].update(epsilon_b_integer_bounds=['-1', '0']),
           'nonnegative remainder bounds required')
    mutate('wrong gap order', lambda x: x[0]['rows'][0].update(H_integer_bounds=[str(4 * DEN)] * 2),
           'positive interval-separation gap required')
    rejected('strict equality rejected', lambda: strict_claim(F(1), F(1)), 'strict lower-bound claim not certified')
    rejected('excessive lower bound', lambda: derive(radial, operator, F('0.000018392')),
             'strict lower-bound claim not certified')
    return results


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--input-dir', type=Path, default=Path(__file__).resolve().parent)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    radial = json.loads((args.input_dir / 'RADIAL_VALUE_CERTIFICATE.json').read_text())
    operator = json.loads((args.input_dir / 'OPERATOR_VALUE_CERTIFICATE.json').read_text())
    result = derive(radial, operator)
    result['negative_probes'] = negative_probes(radial, operator)
    result['negative_probe_count'] = len(result['negative_probes'])
    rendered = json.dumps(result, indent=2) + '\n'
    output = args.output if args.output is not None else args.input_dir / 'OSCILLATION_BOUND_CERTIFICATE.json'
    output.write_text(rendered)
    print(rendered, end='')


if __name__ == '__main__':
    main()
