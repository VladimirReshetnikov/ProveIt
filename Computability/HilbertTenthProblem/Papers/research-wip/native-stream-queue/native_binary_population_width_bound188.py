"""Remove the population recoder's redundant private geometry bound.

The retained positive duration equation implies J>=B and hence
(2^k-1)J>B for k>=3.  The deleted slack is restored positively at zeros;
its off-zero restoration is an integer polynomial, possibly negative.
"""
import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path
import random

import native_binary_population_width_recoder as parent

raw = parent.parent
units = parent.units
BOUND_ROW = ('geo__geometry_index_bound', '+', 'B', 'geo__index_beta')
BOUND_PAIR = ('geo__geometry_index_bound', 'geometry_index')
BOUND_AUX = 'geo__index_beta'


def remove_bound(old):
    """Project a raw population-width packet, including a complete compiler.

    Call after population_width_recoder.rewrite and before unit rewrites.
    Opaque fixed numerals retain the caller's exact fixed-role definitions.
    The supplied duration may be replaced by a syntactically positive
    addition/multiplication expression, as in the compressed tag compiler.
    """
    k = old['width']
    assert isinstance(k, int) and k >= 3
    assert old.get('population_width') and old.get('form', 'raw') == 'raw'
    assert not old.get('unit_factors')
    assert old['geometry_scale'] == 'Q' and old['geometry_input'] == 'geometry_index'
    assert old['width_constraint_operations'] == 2
    assert old['repeated_mask_definition'] == '2^width-1'
    rows = {n: (op, a, b) for n, op, a, b in old['source']}
    assert len(rows) == len(old['source'])
    assert rows[BOUND_ROW[0]] == BOUND_ROW[1:]
    assert old['comparisons'].count(BOUND_PAIR) == 1
    assert old['auxiliaries'].count(BOUND_AUX) == 1
    assert BOUND_AUX not in old['parameters']
    # The witness and its defining register must really be private.
    assert [n for n, _, a, b in old['source'] if BOUND_AUX in (a, b)] == [BOUND_ROW[0]]
    assert not any(BOUND_AUX in pair for pair in old['comparisons'])
    assert not any(BOUND_ROW[0] in (a, b) for _, _, a, b in old['source'])
    assert [pair for pair in old['comparisons'] if BOUND_ROW[0] in pair] == [BOUND_PAIR]
    assert not {BOUND_AUX, BOUND_ROW[0]} & set(old.get('public_registers', {}).values())
    assert rows['Q'] == ('+', 'q', 'power_gap')
    assert rows['Bm1'] == ('-', 'B', 1)
    op, multiplier, right = rows['geometry_index']
    assert op == '*' and right == 'J'
    if isinstance(multiplier, int):
        assert multiplier.bit_length() == k and multiplier & (multiplier + 1) == 0
    else:
        role = getattr(multiplier, 'name', None)
        assert old.get('fixed_numerals', {}).get(role) in ('2^D-1', '2^width-1')
    assert rows['duration_multiple'] == ('*', 'Bm1', 'duration_quotient')
    op, first, duration = rows['duration_J']
    assert (op, first) == ('+', 'duration_multiple')
    assert rows['duration_bound'] == ('+', duration, 'duration_slack')
    assert ('duration_J', 'J') in old['comparisons']
    assert ('duration_bound', 'Bm1') in old['comparisons']
    assert 'duration_quotient' in old['auxiliaries']
    assert 'duration_slack' in old['auxiliaries']
    inputs = set(old['parameters'] + old['auxiliaries'])

    def positive_expression(value, visiting=frozenset()):
        if isinstance(value, int):
            return value > 0
        if value in inputs:
            return True
        if not isinstance(value, str) or value in visiting or value not in rows:
            return False
        op, a, b = rows[value]
        return op in ('+', '*') and positive_expression(a, visiting | {value}) \
            and positive_expression(b, visiting | {value})

    assert positive_expression(duration)
    pair_index = old['comparisons'].index(BOUND_PAIR)
    packet = dict(old,
                  source=[row for row in old['source'] if row[0] != BOUND_ROW[0]],
                  comparisons=[pair for pair in old['comparisons'] if pair != BOUND_PAIR],
                  auxiliaries=[n for n in old['auxiliaries'] if n != BOUND_AUX],
                  population_bound_removed=True,
                  removed_geometry_bound=dict(row=BOUND_ROW, comparison=BOUND_PAIR,
                                              auxiliary=BOUND_AUX, duration=duration),
                  geometry_bound_restoration='geometry_index-B; positive at full zeros')
    if 'boundary_comparisons' in old:
        packet['boundary_comparisons'] = old['boundary_comparisons'] - \
            int(pair_index < old['boundary_comparisons'])
    parent.recount(packet)
    assert packet['operations'] == old['operations'] - 1
    assert packet['multiplications'] == old['multiplications']
    assert packet['additions_subtractions'] == old['additions_subtractions'] - 1
    assert packet['equations'] == old['equations'] - 1
    assert packet['witnesses'] == old['witnesses'] - 1
    return packet


def build(width=3, form='normalized'):
    assert form in ('raw', 'units', 'normalized')
    packet = remove_bound(parent.build(width, 'raw'))
    if form != 'raw':
        packet = units.rewrite(packet, normalize_strong=form == 'normalized')
    packet['form'] = form
    return packet


polynomial_source = parent.polynomial_source
degree_bound = parent.degree_bound


def lift_bound(packet, values):
    """Exact integer lift; positivity of this added value is a zero-set fact."""
    env = raw.execute(packet['source'], values)
    return dict(values, **{BOUND_AUX: env['geometry_index'] - env['B']})


def independent_raw(packet, values):
    """Use the parent's separately stated raw kernels, deleting only its bound."""
    old = parent.build(packet['width'], 'raw')
    residuals = parent.independent_raw(old, lift_bound(packet, values))
    i = old['comparisons'].index(BOUND_PAIR)
    assert residuals[i] == 0
    assert packet['comparisons'] == old['comparisons'][:i] + old['comparisons'][i+1:]
    return residuals[:i] + residuals[i+1:]


def audit_projection(old, packet, values):
    """All-integer source/output identity after the explicit slack lift."""
    before = raw.execute(old['source'], lift_bound(packet, values))
    after = raw.execute(packet['source'], values)
    assert packet['auxiliaries'] == [n for n in old['auxiliaries'] if n != BOUND_AUX]
    assert packet['source'] == [row for row in old['source'] if row[0] != BOUND_ROW[0]]
    assert all(after[n] == before[n] for n, _, _, _ in packet['source'])
    assert before[BOUND_ROW[0]] == before['geometry_index']
    old_pairs = old['comparisons']
    i = old_pairs.index(BOUND_PAIR)
    assert packet['comparisons'] == old_pairs[:i] + old_pairs[i+1:]
    get = lambda v, env: env[v] if isinstance(v, str) else v
    residuals = [get(a, after)-get(b, after) for a, b in packet['comparisons']]
    assert residuals == [get(a, before)-get(b, before) for a, b in old_pairs if (a, b) != BOUND_PAIR]
    source, out = polynomial_source(packet)
    old_source, old_out = parent.polynomial_source(old)
    assert raw.execute(source, values)[out] == raw.execute(old_source, lift_bound(packet, values))[old_out]
    return before[BOUND_AUX]


def ledger(packet):
    source, out = polynomial_source(packet)
    counts = Counter('M' if op == '*' else 'A' for _, op, _, _ in source)
    result = dict(width=packet['width'], form=packet['form'],
                  certificate={k: packet[k] for k in ('operations', 'multiplications',
                               'additions_subtractions', 'equations', 'witnesses')},
                  polynomial=dict(operations=len(source), multiplications=counts['M'],
                                  additions_subtractions=counts['A'], output=out),
                  degree_upper_bound=degree_bound(packet))
    expected = {'raw': (137, 69, 68, 35, 52, 241, 104, 137, 52),
                'units': (143, 75, 68, 16, 39, 190, 91, 99, 195),
                'normalized': (147, 79, 68, 14, 39, 188, 93, 95, 303)}[packet['form']]
    actual = (packet['operations'], packet['multiplications'], packet['additions_subtractions'],
              packet['equations'], packet['witnesses'], len(source), counts['M'], counts['A'],
              result['degree_upper_bound'])
    assert actual == expected, (actual, expected)
    return result


def verify():
    rng = random.Random(188390303)
    records = []
    raw_cases = projection_cases = unit_cases = signed = negative_lifts = 0
    for k in (3, 4, 7, 16, 64, 257):
        for form in ('raw', 'units', 'normalized'):
            old, packet = parent.build(k, form), build(k, form)
            records.append(ledger(packet))
            for case in range(32):
                values = {n: rng.randrange(1, 6) if case < 16 else rng.randrange(-3, 5)
                          for n in packet['parameters']+packet['auxiliaries']}
                slack = audit_projection(old, packet, values)
                projection_cases += 1
                negative_lifts += slack < 0
                signed += case >= 16
                if form == 'raw':
                    env = raw.execute(packet['source'], values)
                    residuals = independent_raw(packet, values)
                    assert residuals == [env[a]-env[b] for a, b in packet['comparisons']]
                    source, out = polynomial_source(packet)
                    assert raw.execute(source, values)[out] == sum(r*r for r in residuals)
                    raw_cases += 1
                else:
                    units.audit_identity(packet, values)
                    unit_cases += 1
    # Duration/geometry-bound implications are checked before any native typing.
    positive_duration = 0
    for k in (3, 4, 9, 33):
        for _ in range(64):
            x, input_slack, gap, v, ell = [rng.randrange(1, 10) for _ in range(5)]
            q = x+input_slack
            Q, J = q+gap, None
            B = (1 << (k-1))*Q
            J = (B-1)*v+ell
            R = ((1 << k)-1)*J
            assert B >= 12 and J >= B and R >= 7*B > B > Q
            assert R-B > 0
            positive_duration += 1
    outer = dyadic = 0
    for k in (3, 5, 17, 65):
        for n in range(2, 10):
            for x in {1, (1 << n)-1, 1 << (n-1), rng.randrange(1, 1 << n)}:
                values = parent.outer_fixture(k, n, x)
                B = (1 << (k-1))*(values['q']+values['power_gap'])
                R = ((1 << k)-1)*values['J']
                assert R-B > 0 and values['duration_quotient'] > 0
                outer += 1
                dyadic += n & (n-1) == 0
    # Explicitly exhibit the limit of the projection: a positive off-zero
    # supplied tuple can have a negative restored index slack.
    packet = build(3, 'raw')
    values = {n: 1 for n in packet['parameters']+packet['auxiliaries']}
    assert lift_bound(packet, values)[BOUND_AUX] == -1
    # Audit the public generic API on complete compressed raw packets,
    # including their computed positive program-dependent duration.
    import binary_tag_parameterized_compressed_compiler as complete
    generic = []
    generic_identity_cases = 0
    for D in (3, 7, 64):
        encoded_length = len(complete.parent.tag.encode('bcb', 3))
        old = parent.rewrite(complete.raw_build(D, 3, encoded_length), complete.Numeral('repunit_divisor'))
        packet = remove_bound(old)
        complete.check_source(packet)
        assert packet['removed_geometry_bound']['duration'] == 'program_duration_bound'
        assert packet['boundary_comparisons'] == old['boundary_comparisons']-1
        assert packet['fixed_numerals'] == old['fixed_numerals']
        # The existing complete unit and normalization guards must still pass.
        unit = complete.parent.units.rewrite(packet)
        normalized = complete.parent.normalized.rewrite(dict(unit, unit_product=True, form='units'))
        constants = complete.numerical_constants(D, 3, 'bcb')
        literal_old = dict(old, source=complete.materialize(old['source'], constants))
        literal_new = dict(packet, source=complete.materialize(packet['source'], constants))
        for case in range(16):
            values = {n: rng.randrange(1, 4) if case < 8 else rng.randrange(-2, 3)
                      for n in packet['parameters']+packet['auxiliaries']}
            audit_projection(literal_old, literal_new, values)
            generic_identity_cases += 1
        generic.append(dict(width=D, raw_operations=packet['operations'],
                            raw_equations=packet['equations'], raw_witnesses=packet['witnesses'],
                            unchanged_fixed_numeral_roles=sorted(packet['fixed_numerals']),
                            complete_unit_guards_pass=True,
                            complete_normalization_guards_pass=True))
    # Each public guard rejects a concrete contract violation.
    base = parent.build(3, 'raw')
    bad = [dict(base, source=[(n, '-', a, b) if n == BOUND_ROW[0] else (n, op, a, b)
                              for n, op, a, b in base['source']]),
           dict(base, source=base['source']+[('bound_leak', '+', BOUND_AUX, 1)]),
           dict(base, comparisons=base['comparisons']+[(BOUND_ROW[0], 'B')]),
           dict(base, auxiliaries=base['auxiliaries']+[BOUND_AUX]),
           dict(base, comparisons=[p for p in base['comparisons'] if p != ('duration_J', 'J')]),
           dict(base, source=[(n, op, a, 'duration_slack') if n == 'duration_J' else (n, op, a, b)
                              for n, op, a, b in base['source']]),
           parent.build(3, 'units')]
    for malformed in bad:
        try:
            remove_bound(malformed)
        except AssertionError:
            pass
        else:
            raise AssertionError('malformed private-bound contract was accepted')
    packet = build(3)
    source, out = polynomial_source(packet)
    encoded = [list(row) for row in source]
    return dict(status='PASS_NATIVE_BINARY_POPULATION_WIDTH_BOUND188', ledgers=records,
                checks=dict(signed_and_positive_source_projection_cases=projection_cases,
                            independently_stated_raw_residual_and_SOS_cases=raw_cases,
                            complete_unit_correction_cases=unit_cases, signed_cases=signed,
                            negative_off_zero_slack_lifts=negative_lifts,
                            untyped_positive_duration_implications=positive_duration,
                            genuine_outer_cases=outer, dyadic_outer_cases=dyadic,
                            nondyadic_outer_cases=outer-dyadic,
                            explicit_positive_off_zero_negative_slack=True,
                            complete_compressed_raw_identity_cases=generic_identity_cases,
                            rejected_malformed_API_contracts=len(bad)),
                complete_raw_API_checks=generic,
                example=dict(parameters=packet['parameters'], auxiliaries=packet['auxiliaries'],
                             source=encoded, comparisons=packet['comparisons'], output=out,
                             source_sha256=hashlib.sha256(json.dumps(encoded).encode()).hexdigest()),
                scope='For fixed width k>=3, the same complete positive dyadic-duration spread '
                      'relation has188 polynomial operations and39 positive witnesses. The '
                      'deleted slack is positive only on the retained zero set. No universal '
                      'tag composition or exact-degree claim is made here.')


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--write', action='store_true')
    args = parser.parse_args()
    result = json.loads(json.dumps(verify()))
    path = Path(__file__).with_suffix('.json')
    if args.write:
        path.write_text(json.dumps(result, indent=2)+'\n')
    else:
        assert json.loads(path.read_text()) == result, 'receipt mismatch'
    print(result['status'])
    print(result['ledgers'][-1])
