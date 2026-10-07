#!/usr/bin/env python3
"""Offline exact checks and stage-100 amplitude certificates for Report190."""
from __future__ import annotations
import argparse
import copy
from fractions import Fraction
import hashlib
import json
from pathlib import Path
import re
import sys

sys.dont_write_bytecode = True
ROOT = Path(__file__).absolute().parent.parent
sys.path.insert(0, str(ROOT))
sys.path.insert(0, str(ROOT / 'code'))
import verify_manifest as manifest
from spiral import delay_table, values, coordinate_model, validate_rows
from exact_arithmetic import (Phi, amplitude_certificate, phi_bracket,
                              outward_decimal, scaled_floor, first_correction)
import independent_certificate as independent

FIXTURE_SHA256 = 'f00dac9c0a61db7a1f77f1ca20db09c495bd1992d003d223c2ab6f3ce4b3b454'
STAGE = 100


def need(condition, message):
    if not condition:
        raise ValueError(message)


def canonical(value):
    return (json.dumps(value, sort_keys=True, indent=2, allow_nan=False) + '\n').encode('utf-8')


def validate_fixture(data):
    need(type(data) is dict and set(data) == {
        'schema', 'retrieved_utc_date', 'integer_sequences', 'amplitudes'}, 'fixture schema')
    need(data['schema'] == 'report190-bounded-oeis-fixtures-v1'
         and data['retrieved_utc_date'] == '2026-10-04', 'fixture identity/date')
    rows = data['integer_sequences']
    need(type(rows) is dict and set(rows) == {'A094925', 'A094926'}, 'sequence fixture set')
    for identifier, count, offset in [('A094925', 38, 1), ('A094926', 41, 0)]:
        row = rows[identifier]
        need(type(row) is dict and set(row) == {'offset', 'terms', 'source'}, 'term row schema')
        need(type(row['offset']) is int and row['offset'] == offset, 'term offset')
        need(type(row['terms']) is list and len(row['terms']) == count, 'term count')
        need(all(type(v) is int and v >= 0 for v in row['terms']), 'term integer domain')
        need(row['source'] == 'https://github.com/oeis/oeisdata/blob/main/seq/'
             + identifier[:4] + '/' + identifier + '.seq', 'term source')
    amps = data['amplitudes']
    need(type(amps) is dict and set(amps) == {'A094925', 'A258639'}, 'amplitude fixture set')
    for identifier, count in [('A094925', 77), ('A258639', 106)]:
        row = amps[identifier]
        need(type(row) is dict and set(row) == {'fractional_digits', 'source'}, 'digit row schema')
        digits = row['fractional_digits']
        need(type(digits) is str and re.fullmatch('[0-9]{' + str(count) + '}', digits),
             'digit fixture length/domain')
        need(row['source'] == 'https://github.com/oeis/oeisdata/blob/main/seq/'
             + identifier[:4] + '/' + identifier + '.seq', 'digit source')
    return data


def parse_fixture(raw):
    need(type(raw) is bytes, 'fixture input must be bytes')
    need(hashlib.sha256(raw).hexdigest() == FIXTURE_SHA256, 'bounded fixture checksum mismatch')
    return validate_fixture(manifest.load_json(raw.decode('utf-8')))


def rational_record(value):
    # Hexadecimal avoids Python's version-dependent decimal integer conversion limit.
    return {'numerator_hex': hex(value.numerator), 'denominator_hex': hex(value.denominator)}


def interval_record(bounds):
    lo, hi = bounds
    need(lo <= hi, 'amplitude interval order')
    lower = outward_decimal(lo, 110)
    upper = outward_decimal(hi, 110, True)
    z = scaled_floor(lo, 120)
    need(z == scaled_floor(hi, 120), '120-place truncation not certified')
    lower_digits, upper_digits = lower.split('.')[1], upper.split('.')[1]
    common = 0
    for a, b in zip(lower_digits, upper_digits):
        if a != b:
            break
        common += 1
    scale = 10 ** 120
    return {'lower_110_places': lower, 'upper_110_places': upper,
            'printed_common_fractional_prefix_digits': common,
            'truncated_fractional_digits_verified_at_least': 120,
            'certified_120_place_truncation': str(z // scale) + '.' + str(z % scale).zfill(120),
            'exact_lower': rational_record(lo), 'exact_upper': rational_record(hi)}


def rejected(call):
    try:
        call()
    except (TypeError, ValueError, ZeroDivisionError):
        return
    raise ValueError('invalid input unexpectedly accepted')


def input_guards(fixture, raw):
    cases = []
    for invalid in (True, 1.0, '1', None, Fraction(1), -1):
        cases += [lambda v=invalid: delay_table(v), lambda v=invalid: coordinate_model(v),
                  lambda v=invalid: values(delay_table(1), v)]
    for invalid in (True, 1.0, '1', None):
        cases += [lambda v=invalid: Phi(v), lambda v=invalid: Phi(0, v),
                  lambda v=invalid: Phi(1) ** v, lambda v=invalid: independent.pair(v),
                  lambda v=invalid: independent.power(independent.pair(1), v)]
    for invalid in (0, -1, True, 1.0):
        cases += [lambda v=invalid: phi_bracket(v),
                  lambda v=invalid: amplitude_certificate(v, [0, 1, 1]),
                  lambda v=invalid: values(delay_table(1), 0, v)]
    bad_rows = [None, (), [], [(), (), (0,)], [(), (), (), []],
                [(), (), (), (-1,)], [(), (), (), (True,)],
                [(), (), (), (1,)], [(), (), (), (0, 0)], [(), (), (), (2, 0)]]
    cases += [lambda r=r: validate_rows(r) for r in bad_rows]
    cases += [lambda: Phi().inverse(), lambda: independent.inv(independent.pair()),
              lambda: Phi(1).enclosure(Fraction(2), Fraction(1)),
              lambda: independent.interval(independent.pair(1), Fraction(2), Fraction(1)),
              lambda: amplitude_certificate(1, [0, 1]),
              lambda: independent.certificate(1, 2, 3),
              lambda: independent.certificate(True, 3, 2),
              lambda: outward_decimal(Fraction(1), 0),
              lambda: outward_decimal(Fraction(1), 3, 1),
              lambda: scaled_floor(1.0, 3), lambda: parse_fixture(raw + b' '),
              lambda: parse_fixture(raw.decode('utf-8')),
              lambda: manifest.load_json('{"x":1,"x":2}'),
              lambda: manifest.load_json('{"x":NaN}')]
    mutations = [lambda d: d['integer_sequences']['A094926']['terms'].__setitem__(0, True),
                 lambda d: d['integer_sequences']['A094926'].__setitem__('offset', False),
                 lambda d: d['integer_sequences']['A094925']['terms'].pop(),
                 lambda d: d['amplitudes']['A258639'].__setitem__('fractional_digits', '1'),
                 lambda d: d['amplitudes']['A094925'].__setitem__('fractional_digits', 'x' * 77),
                 lambda d: d.__setitem__('unrecognized', 1),
                 lambda d: d['amplitudes']['A094925'].__setitem__('source', 'https://example.org/')]
    for change in mutations:
        altered = copy.deepcopy(fixture)
        change(altered)
        cases.append(lambda d=altered: validate_fixture(d))
    # Well-typed corruption must also be rejected; structure alone is insufficient.
    for path in ('term', 'digit'):
        altered = copy.deepcopy(fixture)
        if path == 'term':
            altered['integer_sequences']['A094926']['terms'][15] += 1
        else:
            digits = altered['amplitudes']['A258639']['fractional_digits']
            altered['amplitudes']['A258639']['fractional_digits'] = '6' + digits[1:]
        cases.append(lambda d=altered: parse_fixture(canonical(d)))
    for case in cases:
        rejected(case)
    return len(cases)


def first_correction_checks():
    stages = 19
    data = first_correction(stages)
    phi = Phi(0, 1)
    q, rho = phi ** -6, -phi ** -2
    alpha, beta = phi / (2 * phi - 1), 1 / (phi * (2 * phi - 1))
    side_tail_checks = 0
    samples = {0, 1, 2}
    for r in range(1, stages + 1):
        stage_tail = q ** (r + 1) * (phi ** 7 * (r + 1) - phi ** 6 + 2 * phi / (1 - q))
        start = 3 * r * r - 2 * r + 2
        for side in range(6):
            length = r + (side == 4)
            for h in range(1, length + 1):
                n = start + side * r + (side == 5) + h - 1
                remaining = (length - h) * phi ** (5 - side)
                if h < length:
                    remaining = remaining - phi ** (4 - side)
                for later in range(side + 1, 6):
                    remaining = remaining + (r + (later == 4)) * phi ** (5 - later) - phi ** (4 - later)
                expected = q ** r * remaining + stage_tail
                need(data['tail'][n] == expected, 'exact F1 side/corner future-tail identity')
                side_tail_checks += 1
                if r <= 7 and h in (1, length):
                    samples.add(n)
    nmax = len(data['eta']) - 1
    for n in sorted(samples):
        direct_tail = data['tail'][nmax] + sum(data['eta'][n + 1:], Phi())
        direct_past = sum((rho ** (n - m) * data['eta'][m] for m in range(2, n + 1)), Phi())
        need(data['filter'][n] == direct_past, 'exact F1 direct stable convolution')
        need(data['F1'][n] == -alpha * direct_tail + beta * direct_past,
             'exact F1 operator identity')
    return {'side_corner_tail_identities': side_tail_checks,
            'direct_operator_and_stable_convolution_samples': len(samples),
            'stage': stages, 'infinite_future_tail_is_algebraically_summed': True}


def run_checks():
    raw = manifest.read_regular(ROOT / 'data/oeis_fixtures.json', 16384)
    fixture = parse_fixture(raw)
    guards = input_guards(fixture, raw)
    first = first_correction_checks()
    rows = delay_table(STAGE)
    short = delay_table(19)
    p = Phi(0, 1)
    q = p ** -6
    a, b = p ** 7 * (1 - q), p ** 2 - p ** 6
    need(a == Phi(8, 12) and b == Phi(-4, -7), 'stage-weight coefficients')
    need(p ** 2 == p + 1 and p * (p - 1) == 1, 'field relation')
    for r in range(1, 20):
        lo, hi = 3 * r * r - 2 * r + 2, 3 * r * r + 4 * r + 2
        weight = sum((sum((p ** (j - n) for j in short[n]), Phi())
                      for n in range(lo, hi + 1)), Phi())
        need(weight == q ** r * (a * r + b), 'stage weight identity')
        for n in range(lo, hi + 1):
            need(all(6 * r - 4 <= n - j <= 6 * r + 2 for j in short[n]), 'delay range')
    certificates = []
    for seed, identifier in [(0, 'A094926'), (1, 'A094925')]:
        sequence = values(rows, seed)
        geometric, geometric_rows = coordinate_model(STAGE, seed)
        need(geometric_rows[:len(short)] == short, '1162-row coordinate/table agreement')
        need(geometric_rows == rows and geometric == sequence, 'complete stage-100 coordinate replay')
        need(sequence[:len(fixture['integer_sequences'][identifier]['terms'])]
             == fixture['integer_sequences'][identifier]['terms'], 'official integer terms')
        need(all(sequence[n + 1] > sequence[n] for n in range(2, len(sequence) - 1)),
             'finite strict monotonicity')
        cert = amplitude_certificate(STAGE, sequence)
        other = independent.certificate(STAGE, geometric[-1], geometric[-2])
        for key in ('center', 'tail'):
            value = cert[key]
            need(other[key + '_sqrt5'] == (value.a + value.b / 2, value.b / 2),
                 'independent ' + key + ' algebra')
        need(cert['interval'] == other['interval'], 'independent exact amplitude bounds')
        need(cert['original_index_interval'] == other['original_index_interval'],
             'independent original-index bounds')
        record = {'seed_a0': seed, 'seed_a1': 1, 'stage': STAGE, 'N': cert['n'],
                  'phi_enclosure_bits': cert['bits'], 'amplitude': 'C' + str(seed),
                  'independent_sqrt5_arithmetic_agrees': True,
                  'bounds': interval_record(cert['interval']),
                  'tail_upper_125_places': outward_decimal(cert['tail_interval'][1], 125, True)}
        if seed == 1:
            record['original_index_amplitude'] = 'C1/phi'
            record['original_index_bounds'] = interval_record(cert['original_index_interval'])
        id_digits = 'A258639' if seed == 0 else 'A094925'
        digits = fixture['amplitudes'][id_digits]['fractional_digits']
        bounds = cert['interval'] if seed == 0 else cert['original_index_interval']
        need(scaled_floor(bounds[0], len(digits)) == scaled_floor(bounds[1], len(digits))
             == int(digits), 'all source amplitude digits')
        record['source_amplitude_digits_checked'] = {'sequence': id_digits, 'count': len(digits)}
        certificates.append(record)
    return {'status': 'passed', 'report': 190, 'arithmetic': 'integer and Fraction only',
            'required_third_party_dependencies': [], 'fixture_sha256': FIXTURE_SHA256,
            'coordinate_table_rows_checked': len(short),
            'additional_complete_stage_coordinate_rows_checked_per_seed': len(rows),
            'independent_coordinate_sequences_checked': 2,
            'official_integer_terms_checked': 79, 'exact_weight_stage_checks': 19,
            'input_and_fixture_rejection_tests': guards, 'exact_first_correction_checks': first,
            'certificates': certificates,
            'bound_provenance': {
                'center': 'c_N = phi^(-N)(a_N phi+a_(N-1))/(2 phi-1)',
                'tail': 'T_R = phi^(-6(R+1))[phi^7(R+1)-phi^6+2phi/(1-phi^(-6))]',
                'theorem': 'For N=U_R, R>=1 and T_R<1: c_N <= C <= c_N/(1-T_R)',
                'rational_rule': 'If c_N in [cl,ch], T_R in [tl,th], then [cl,ch/(1-th)] encloses C',
                'original_index_rule': 'Divide lower by phi_upper and upper by phi_lower',
                'root_rule': 'D=2^bits; s=isqrt(5D^2); phi in [(D+s)/(2D),(D+s+1)/(2D)]',
                'hex_rationals': 'Each exact endpoint is numerator_hex/denominator_hex',
                'digits_rule': 'floor(10^120 lower)=floor(10^120 upper); display rounding is not used'},
            'scope': 'Finite checks supplement the proofs in Report190. Exact amplitude intervals '
                     'use its proved algebraic tail bound. No finite replay proves an asymptotic theorem.'}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, help='new file outside the source tree')
    args = parser.parse_args()
    try:
        if args.output is not None:
            output = args.output.absolute()
            need('..' not in output.parts, 'unsafe output path')
            manifest.check_directory(output.parent)
            need(not output.resolve().is_relative_to(ROOT.resolve()), 'output must be outside source tree')
            need(not output.exists() and not output.is_symlink(), 'refusing existing output')
        payload = canonical(run_checks())
        if args.output is not None:
            with output.open('xb') as stream:
                stream.write(payload)
        sys.stdout.buffer.write(payload)
    except (ValueError, TypeError, OSError, ZeroDivisionError) as exc:
        print(json.dumps({'status': 'FAIL', 'error': str(exc)}, sort_keys=True), file=sys.stderr)
        return 1
    return 0


if __name__ == '__main__':
    sys.exit(main())
