"""A complete tag compiler with compressed fixed numerals and five program ports.

Numeral atoms denote fixed integers, never hidden runtime arithmetic or
additional parameters. The explicit universal machine application is separate.
"""
import argparse
from collections import Counter
from dataclasses import dataclass
import hashlib
import json
from pathlib import Path
import random

import binary_tag_complete_dyadic_compiler as parent


@dataclass(frozen=True)
class Numeral:
    name: str


PARAMETERS = ['x', 'program_A', 'program_B', 'program_T', 'program_E', 'program_bound']
NUMERALS = {
    'recoder_radix': '2^(D-1)',
    'repunit_divisor': '2^D-1',
    'terminal_scale': '2^(beta+1)',
    'terminal_offset': '2^beta',
    'history_radix': '2^(L+1)',
    'upper_difference': '2^(beta+2)-2',
    'lower_difference': '2^L-2',
    'production_offset': "val(1 e(u without its last b) 10)",
    'upper_offset': '2^(beta+1)+1',
    'upper_constant': '2^(beta+3)+2',
    'lower_constant': '2^L+production_offset+10',
}


def raw_build(D, beta, encoded_production_length):
    assert isinstance(D, int) and D >= 3
    assert isinstance(beta, int) and beta >= 2
    L = encoded_production_length-beta+1
    # Makes the three lower-slope classes distinct and the chosen dyadic
    # radix strictly dominate every affine digit bound.
    assert isinstance(L, int) and L >= beta+3
    sample = parent.build_raw()
    left = parent.recoder.build(3)
    old_chain = parent.recoder.power_chain(3)
    assert left['source'][:len(old_chain)+1] == old_chain+[('B', '*', 4, 'Q')]
    chain = parent.recoder.power_chain(D)
    left_source = chain+[('B', '*', Numeral('recoder_radix'), 'Q')]+left['source'][len(old_chain)+1:]
    duration_alias = lambda v: 'program_duration_bound' if v == 'duration' else v
    left_source = [(n, op, duration_alias(a), duration_alias(b)) for n, op, a, b in left_source]
    left = dict(left, source=left_source, width=D, power_chain_length=len(chain))
    h = sample['history_packet']
    assert h['operations'] == 161 and h['baselines'] == (2, 2)
    assert h['scale_exponent'] == 11
    changes = {
        'B__3': (('*', 'height_sum__2', 65536), 'history_radix'),
        'linear0_coefficient__17': (('*', 'ZUhat0', 30), 'upper_difference'),
        'linear1_coefficient__27': (('*', 'ZVhat0', 32766), 'lower_difference'),
        'linear1_coefficient__29': (('*', 'Shat0', 30918), 'production_offset'),
        'linear_coefficient__165': (('*', 'group_sum__58', 17), 'upper_offset'),
        'linear_constant__168': (('-', 'linear_sum__167', 66), 'upper_constant'),
        'linear_constant__173': (('-', 'linear_sum__172', 63696), 'lower_constant'),
    }
    hsource = []
    found = set()
    for n, op, a, b in h['source']:
        if n in changes:
            expected, key = changes[n]
            assert (op, a, b) == expected
            b = Numeral(key)
            found.add(n)
        hsource.append((n, op, a, b))
    assert found == set(changes)
    # Keep actual fixed-map roles, rather than stale illustrative map numerals.
    h = dict(h, source=hsource, K=Numeral('history_radix'),
             maps_definition='(2,1,2^L,d); (2^(beta+2),2^(beta+1)+1,8,6); '
                             '(2^(beta+2),2^(beta+1)+1,2,0); (2,1,2,0)')
    for key in ('maps', 'groups_U', 'groups_V', 'linear_forms', 'history_candidates',
                'baseline_candidates', 'linear_candidate_ledgers'):
        h.pop(key, None)
    def ha(value):
        if not isinstance(value, str):
            return value
        return {'Vinitial': 'load__tag_input', 'Vfinal': 'hist__tag_terminal',
                'Ufinal': 'hist__Ufinal'}.get(value, 'hist__'+value)
    load = [
        ('load__repunit_product', '*', Numeral('repunit_divisor'), 'load__r'),
        ('load__prefix_data', '*', 'program_A', 'load__r'),
        ('load__data_delta', '*', 'program_B', 'z'),
        ('load__data_body', '+', 'load__prefix_data', 'load__data_delta'),
        ('load__data_counter_scale', '*', 'load__data_body', 'Q'),
        ('load__counter_frame', '*', 'program_T', 'load__r'),
        ('load__before_tail', '+', 'load__data_counter_scale', 'load__counter_frame'),
        ('load__tag_input', '+', 'load__before_tail', 'program_E'),
    ]
    terminal = [
        ('hist__tag_terminal_scale', '*', Numeral('terminal_scale'), 'hist__Ufinal'),
        ('hist__tag_terminal', '+', 'hist__tag_terminal_scale', Numeral('terminal_offset')),
    ]
    source = [('program_duration_bound', '+', 'program_bound', 'program_duration_gap')]
    source += left_source+load+terminal+[(ha(n), op, ha(a), ha(b)) for n, op, a, b in hsource]
    pairs = [(duration_alias(a), duration_alias(b)) for a, b in left['comparisons']]
    pairs += [('load__repunit_product', 'modulus')]
    front_count = len(pairs)
    pairs += [(ha(a), ha(b)) for a, b in h['comparisons']]
    aux = ['z']+[n for n in left['auxiliaries'] if n != 'duration']
    aux += ['load__r', 'program_duration_gap', 'hist__Ufinal']
    aux += [ha(n) for n in h['auxiliaries']]
    packet = dict(source=source, comparisons=pairs, parameters=PARAMETERS,
                  auxiliaries=aux, width=D, beta=beta, encoded_production_length=encoded_production_length,
                  lower_word_length=L, form='raw', history_packet=h,
                  inline_initial=True, program_code=None, loaded_input='x',
                  initial_register='load__tag_input', boundary_comparisons=front_count,
                  tiles=4, layout='slope_classes', fixed_numerals=NUMERALS)
    recount(packet)
    check_source(packet)
    return packet


def recount(packet):
    counts = Counter('M' if op == '*' else 'A' for _, op, _, _ in packet['source'])
    packet.update(operations=len(packet['source']), multiplications=counts['M'],
                  additions_subtractions=counts['A'], equations=len(packet['comparisons']),
                  witnesses=len(packet['auxiliaries']))


def check_source(packet):
    known = set(packet['parameters']+packet['auxiliaries'])
    assert len(known) == len(packet['parameters'])+len(packet['auxiliaries'])
    used = set()
    for n, op, a, b in packet['source']:
        assert n not in known and op in ('+', '-', '*')
        for v in (a, b):
            assert isinstance(v, (str, int, Numeral))
            if isinstance(v, str):
                assert v in known, v
            if isinstance(v, Numeral):
                assert v.name in NUMERALS
                used.add(v.name)
        known.add(n)
    assert used == set(NUMERALS)
    assert all(not isinstance(v, str) or v in known for pair in packet['comparisons'] for v in pair)


def build(D, beta, encoded_production_length, form='normalized'):
    assert form in ('raw', 'units', 'normalized')
    packet = raw_build(D, beta, encoded_production_length)
    if form != 'raw':
        packet = parent.units.rewrite(packet)
        packet.update(unit_product=True, form='units')
        if form == 'normalized':
            packet = parent.normalized.rewrite(packet)
            packet['form'] = 'normalized'
    check_source(packet)
    return packet


def numerical_constants(D, beta, production):
    """Only for small literal checks; never call on the universal production."""
    word = '1'+parent.tag.encode(production[:-1], beta)+'10'
    L, d = len(word), int(word, 2)
    assert L >= beta+3
    return dict(recoder_radix=1 << (D-1), repunit_divisor=(1 << D)-1,
        terminal_scale=1 << (beta+1), terminal_offset=1 << beta,
        history_radix=1 << (L+1), upper_difference=(1 << (beta+2))-2,
        lower_difference=(1 << L)-2, production_offset=d,
        upper_offset=(1 << (beta+1))+1, upper_constant=(1 << (beta+3))+2,
        lower_constant=(1 << L)+d+10)


def materialize(source, constants):
    get = lambda v: constants[v.name] if isinstance(v, Numeral) else v
    return [(n, op, get(a), get(b)) for n, op, a, b in source]


def encode_source(source):
    get = lambda v: {'fixed_numeral': v.name} if isinstance(v, Numeral) else v
    return [[n, op, get(a), get(b)] for n, op, a, b in source]


def degree_upper_bound(packet):
    """Degree propagation only: deliberately does not evaluate huge coefficients.

    The main-norm cancellation is an audited polynomial identity. Claim an
    upper bound here, avoiding any numerical leading-coefficient surrogate.
    """
    degree = {n: 1 for n in packet['parameters']+packet['auxiliaries']}
    d = lambda v: degree[v] if isinstance(v, str) else 0
    rows = {n: (op, a, b) for n, op, a, b in packet['source']}
    overrides = {} if packet['form'] == 'raw' else {
        p+'R15': p for p in ('geo__', 'and__', 'hist__and__')}
    for n, op, a, b in packet['source']:
        degree[n] = d(a)+d(b) if op == '*' else max(d(a), d(b))
        if n in overrides:
            p = overrides[n]
            X, ac, G, aa, cc = (p+k for k in ('wn2', 'cam2', 'gam', 'R12', 'R10a'))
            expected = {p+'R15': ('-', p+'L15', p+'Ac2'),
                p+'R14': ('+', p+'D1', G), p+'D1': ('+', X, ac),
                ac: ('*', cc, aa), G: ('*', p+'ga', p+'a4m5'),
                p+'a4m5': ('+', p+'a4', 3), p+'a4': ('*', 4, aa),
                p+'A': ('+', p+'a_square', p+'a4m5'), p+'a_square': ('*', aa, aa),
                p+'c2': ('*', cc, cc), p+'Ac2': ('*', p+'A', p+'c2'),
                p+'L15': ('*', p+'R14', p+'R14')}
            assert all(rows[key] == value for key, value in expected.items())
            degree[n] = max(2*d(X), d(X)+d(ac), d(X)+d(G),
                            d(ac)+d(G), 2*d(G), d(p+'a4m5')+2*d(cc))
    pairs = packet['comparisons'] if packet['form'] == 'raw' else packet['comparisons'][:-1]
    maximum = max(max(d(a), d(b)) for a, b in pairs)
    unit_degree = 0 if packet['form'] == 'raw' else d(packet['unit_register'])
    closed = {'raw': 132*packet['width']+412,
              'units': 342*packet['width']+1042,
              'normalized': 544*packet['width']+1660}
    assert unit_degree+2*maximum == closed[packet['form']]
    return dict(degree_upper_bound=unit_degree+2*maximum,
                unit_degree_bound=unit_degree, maximum_residual_degree_bound=maximum,
                history_scale_exponent=packet['history_packet']['scale_exponent'],
                history_scale_degree_bound=d('hist__and__q'),
                recoder_scale_degree_bound=d('and__q'),
                exact_degree_claimed=False)


def ledger(packet):
    source, out = parent.polynomial_source(packet)
    counts = Counter('M' if op == '*' else 'A' for _, op, _, _ in source)
    mu = packet['width'].bit_length()+packet['width'].bit_count()-2
    expected = {'raw': (475, 88, 56), 'units': (400, 69, 28), 'normalized': (397, 69, 25)}
    baseline, witnesses, equations = expected[packet['form']]
    assert len(source) == baseline+mu and packet['witnesses'] == witnesses
    assert packet['equations'] == equations
    return dict(form=packet['form'], width=packet['width'], beta=packet['beta'],
        lower_word_length=packet['lower_word_length'], power_chain_operations=mu,
        certificate={k: packet[k] for k in ('operations', 'multiplications', 'additions_subtractions',
                                           'equations', 'witnesses')},
        polynomial=dict(operations=len(source), multiplications=counts['M'],
                        additions_subtractions=counts['A'], output=out),
        parameters=packet['parameters'], **degree_upper_bound(packet))


def reference_raw(blocks, production):
    """Independent literal compiler, changing only the documented program ports."""
    packet = parent.build_raw(blocks, production)
    source = []
    roles = {'load__prefix_data': 'program_A', 'load__data_delta': 'program_B',
             'load__counter_frame': 'program_T', 'load__tag_input': 'program_E'}
    for n, op, a, b in packet['source']:
        if n in roles:
            if n == 'load__tag_input':
                b = roles[n]
            else:
                a = roles[n]
        source.append((n, op, a, b))
    alias = lambda v: 'program_duration_bound' if v == 'duration' else v
    source = [('program_duration_bound', '+', 'program_bound', 'program_duration_gap')]+[
        (n, op, alias(a), alias(b)) for n, op, a, b in source]
    pairs = [(alias(a), alias(b)) for a, b in packet['comparisons']]
    packet = dict(packet, source=source, comparisons=pairs, parameters=PARAMETERS,
                  auxiliaries=[n for n in packet['auxiliaries'] if n != 'duration']+['program_duration_gap'])
    recount(packet)
    return packet


def verify():
    import sympy as sp
    t, R, d, HU, HV, ZU, ZV0, ZV1, S0, S1, S2, S3 = sp.symbols(
        't R d HU HV ZU ZV0 ZV1 S0 S1 S2 S3')
    grouped_U = 2*HU+(4*t-2)*ZU+(2*t+1)*(S1+S2)+S0+S3-(8*t+2)
    literal_U = 2*HU+(4*t-2)*(ZU-1)+(S0-1)+(2*t+1)*(S1-1)+(2*t+1)*(S2-1)+(S3-1)
    grouped_V = 2*HV+(R-2)*ZV0+d*S0+6*(S1+ZV1)-(R+d+10)
    literal_V = 2*HV+(R-2)*(ZV0-1)+6*(ZV1-1)+d*(S0-1)+6*(S1-1)
    assert sp.expand(grouped_U-literal_U) == sp.expand(grouped_V-literal_V) == 0
    rng = random.Random(560400)
    records = []
    identities = signed = outer = 0
    for beta in (2, 3, 4, 7):
        blocks = parent.example_blocks(beta)
        production = 'c'*(beta-1)+'b'*beta
        D = blocks['constants']['D']
        constants = numerical_constants(D, beta, production)
        before = reference_raw(blocks, production)
        for form in ('raw', 'units', 'normalized'):
            packet = build(D, beta, len(parent.tag.encode(production, beta)), form)
            reference = before
            if form != 'raw':
                reference = parent.units.rewrite(reference)
                reference.update(form='units', unit_product=True)
                if form == 'normalized':
                    reference = parent.normalized.rewrite(reference)
                    reference['form'] = form
            source, out = parent.polynomial_source(packet)
            literal = materialize(source, constants)
            refsource, refout = parent.polynomial_source(reference)
            assert set(packet['auxiliaries']) == set(reference['auxiliaries'])
            for case in range(24):
                values = {n: rng.randrange(1, 6) if case < 12 else rng.randrange(-3, 4)
                          for n in packet['parameters']+packet['auxiliaries']}
                env = parent.execute(literal, values)
                refenv = parent.execute(refsource, values)
                assert env[out] == refenv[refout]
                assert [parent.scalar(a, env)-parent.scalar(b, env) for a, b in packet['comparisons']] == [
                    parent.scalar(a, refenv)-parent.scalar(b, refenv) for a, b in reference['comparisons']]
                identities += 1
                signed += case >= 12
            records.append(ledger(packet))
        c = blocks['constants']
        for n in (2, 4, 8):
            for x in (1, 2**n-1):
                Q, z = 1 << (D*n), parent.boundary.spread(x, D)
                r = (Q-1)//c['L']
                code = ((c['A']*r+c['B']*z)*Q+c['T']*r+c['E'])
                assert code == int('1'+parent.boundary.frame(c, format(x, f'0{n}b')), 2)
                assert n == 1+(n-1) and min(c['A'], c['B'], c['T'], c['E']) > 0
                outer += 1
    # An enormous exponent tests actual chain construction and literal counts,
    # without allocating any integer with this many bits.
    giant = build((1 << 109)+123456, 1000, 10**20)
    giant_ledger = ledger(giant)
    source, out = parent.polynomial_source(giant)
    encoded = encode_source(source)
    example = build(6, 3, len(parent.tag.encode('ccbbb', 3)))
    es, eo = parent.polynomial_source(example)
    return dict(status='PASS_BINARY_TAG_PARAMETERIZED_COMPRESSED_COMPILER',
        symbolic_transport_identities=2,
        ledgers=records, full_output_identities=identities, signed_cases=signed,
        literal_parameter_slice_frames=outer, giant_exponent_ledger=giant_ledger,
        giant_source_sha256=hashlib.sha256(json.dumps(encoded, sort_keys=True).encode()).hexdigest(),
        fixed_numeral_definitions=NUMERALS,
        example=dict(ledger=ledger(example), source=encode_source(es), output=eo,
                     parameters=example['parameters'], auxiliaries=example['auxiliaries'],
                     comparisons=example['comparisons']),
        scope='Complete five-program-parameter tag-word-family compiler with compressed fixed '
              'numerals. An explicit universal table application remains separate. Degree '
              'bounds only; no astronomical Pell zero or giant fixed integer materialized.')


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
    print(result['giant_exponent_ledger'])
