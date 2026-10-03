"""Two native unit cores for the complete U9 joint-AND construction."""
import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path
import random

import neary_woods_universal_joint_and as raw
import native_binary_input_dilation_unit179 as units
import pcp_normalized_strong_history_units as strong
import neary_woods_universal_population_tag as constants_parent

compiler = constants_parent.compiler
PREFIXES = ('geo__', 'and__')


def normalize(base):
    assert tuple(base['core_prefixes']) == PREFIXES
    assert len(base['unit_factors']) == 7
    assert base['unit_factors'].count('and__bs_q') == 1
    rebuilt = {p+n for p in PREFIXES for n in ('f', 'i', 'j', 'o', 'y_aux')}
    deps = {n: {n} for n in base['parameters']+base['auxiliaries']}
    get = lambda v: deps[v] if isinstance(v, str) else set()
    for n, _, a, b in base['source']:
        deps[n] = get(a) | get(b)
    for p in PREFIXES:
        for field in ('f', 'i', 'j', 'o', 'y_aux'):
            assert all(n.startswith(p) for n, _, a, b in base['source'] if p+field in (a, b))
    exceptions = {(p+'ic22', p+'R16') for p in PREFIXES} | {
                  (p+'H17', p+'aux_u_rhs') for p in PREFIXES}
    for a, b in base['comparisons'][:-1]:
        if (a, b) not in exceptions:
            assert not (get(a) | get(b)) & rebuilt
    for factor in base['unit_factors']:
        if factor not in {p+'P17' for p in PREFIXES}:
            assert not get(factor) & rebuilt
    p = base
    for prefix in PREFIXES:
        p = strong.rewrite(dict(p, core_prefix=prefix, scale_exponent=1))
    p = dict(p, form='normalized', parent_packet=base,
             normalized_strong_factors=[q+'f_square_minus_one' for q in PREFIXES],
             removed_strong_comparisons=[(q+'ic22', q+'R16') for q in PREFIXES],
             normalized_two_core=True)
    for key in ('exact_degree', 'alternative_SOS_degree', 'normalized_strong_factor',
                'removed_strong_comparison', 'core_prefix', 'scale_exponent'):
        p.pop(key, None)
    assert p['operations'] == base['operations']+4
    assert p['equations'] == base['equations']-2
    assert p['auxiliaries'] == base['auxiliaries']
    compiler.check_source(p)
    return p


def build(form='normalized', *, merge_bound=True):
    assert form in ('raw', 'units', 'normalized')
    original = raw.build(merge_bound=merge_bound)
    if form == 'raw':
        return original
    base = units.rewrite(original)
    base.update(form='units', raw_parent=original, unit_product=True,
                native_prefixes=list(PREFIXES))
    assert (base['operations'], base['equations'], base['witnesses']) == (252, 18, 51)
    packet = normalize(base) if form == 'normalized' else base
    compiler.check_source(packet)
    return packet


def polynomial_source(packet):
    return raw.polynomial_source(packet) if packet['form'] == 'raw' else units.polynomial_source(packet)


def degree_bound(packet):
    degrees = {n: 1 for n in packet['parameters']+packet['auxiliaries']}
    d = lambda v: degrees[v] if isinstance(v, str) else 0
    rows = {n: (op, a, b) for n, op, a, b in packet['source']}
    for n, op, a, b in packet['source']:
        degrees[n] = d(a)+d(b) if op == '*' else max(d(a), d(b))
        if packet['form'] != 'raw' and n in {p+'R15' for p in PREFIXES}:
            p = n[:-3]
            X, ac, G, aa, cc = (p+k for k in ('wn2', 'cam2', 'gam', 'R12', 'R10a'))
            expected = {p+'R15': ('-', p+'L15', p+'Ac2'),
                p+'R14': ('+', p+'D1', G), p+'D1': ('+', X, ac),
                ac: ('*', cc, aa), G: ('*', p+'ga', p+'a4m5'),
                p+'a4m5': ('+', p+'a4', 3), p+'a4': ('*', 4, aa),
                p+'A': ('+', p+'a_square', p+'a4m5'), p+'a_square': ('*', aa, aa),
                p+'c2': ('*', cc, cc), p+'Ac2': ('*', p+'A', p+'c2'),
                p+'L15': ('*', p+'R14', p+'R14')}
            assert all(rows[key] == value for key, value in expected.items())
            degrees[n] = max(2*d(X), d(X)+d(ac), d(X)+d(G),
                             d(ac)+d(G), 2*d(G), d(p+'a4m5')+2*d(cc))
    is_raw = packet['form'] == 'raw'
    pairs = packet['comparisons'] if is_raw else packet['comparisons'][:-1]
    residual = max(max(d(a), d(b)) for a, b in pairs)
    product = 0 if is_raw else d(packet['unit_register'])
    return dict(degree_upper_bound=product+2*residual, unit_degree_bound=product,
                maximum_residual_degree_bound=residual,
                factor_degree_bounds={n: d(n) for n in packet.get('unit_factors', [])},
                native_scale_degrees=[d('Q'), d('and__q')], exact_degree_claimed=False)


def ledger(packet):
    source, output = polynomial_source(packet)
    cc = Counter('M' if op == '*' else 'A' for _, op, _, _ in source)
    expected = {'raw': (246, 37, 64, 356, 155, 201),
                'units': (252, 18, 51, 305, 142, 163),
                'normalized': (256, 16, 51, 303, 144, 159)}[packet['form']]
    assert (packet['operations'], packet['equations'], packet['witnesses'],
            len(source), cc['M'], cc['A']) == expected
    return dict(form=packet['form'], bound_is_program_E=packet['bound_is_program_E'],
                certificate={k: packet[k] for k in ('operations', 'multiplications',
                         'additions_subtractions', 'equations', 'witnesses')},
                polynomial=dict(operations=len(source), multiplications=cc['M'],
                         additions_subtractions=cc['A'], output=output),
                parameters=packet['parameters'], **degree_bound(packet))


def normalized_lift(packet, values):
    env = compiler.parent.execute(packet['source'], values)
    return dict(values, **{p+'i': env[p+'A']*values[p+'i'] for p in PREFIXES})


def audit_normalized(packet, values):
    old = packet['parent_packet']
    env = compiler.parent.execute(packet['source'], values)
    restored = normalized_lift(packet, values)
    before = compiler.parent.execute(old['source'], restored)
    factors = {}
    for p in PREFIXES:
        N, Delta = env[p+'f_square_minus_one'], env[p+'A']
        residual = before[p+'ic22']-before[p+'R16']
        assert residual == Delta*(1-N)
        factors[p+'P17'] = before[p+'P17']+residual*env[p+'aux_square_gap']
        factors[p+'f_square_minus_one'] = N
    for name in old['unit_factors']:
        if name not in factors:
            factors[name] = before[name]
        assert env[name] == factors[name]
    scalar = compiler.parent.scalar
    removed = set(packet['removed_strong_comparisons'])
    rr = [scalar(a, before)-scalar(b, before) for a, b in old['comparisons'][:-1]
          if (a, b) not in removed]
    assert rr == [scalar(a, env)-scalar(b, env) for a, b in packet['comparisons'][:-1]]
    product = 1
    for name in packet['unit_factors']:
        assert env[name] == factors[name]
        product *= factors[name]
    assert env[packet['unit_register']] == product
    source, out = polynomial_source(packet)
    assert compiler.parent.execute(source, values)[out] == product*(1+sum(r*r for r in rr))-1
    if all(v > 0 for v in values.values()):
        assert all(v > 0 for v in restored.values())
    return restored


def verify():
    rng = random.Random(303144159)
    records, corrections, norm_cases, signed = [], 0, 0, 0
    for merge_bound in (False, True):
        for form in ('raw', 'units', 'normalized'):
            packet = build(form, merge_bound=merge_bound)
            records.append(ledger(packet))
            if form == 'raw':
                continue
            for case in range(64):
                pos = case < 32
                C = {n: rng.randrange(1, 8) if pos else rng.randrange(-5, 6)
                     for n in compiler.NUMERALS}
                if pos:
                    C['recoder_radix'], C['repunit_divisor'] = 4, 7
                literal = constants_parent.materialize_packet(packet, C)
                values = {n: rng.randrange(1, 5) if pos else rng.randrange(-3, 4)
                          for n in packet['parameters']+packet['auxiliaries']}
                if form == 'normalized':
                    values = audit_normalized(literal, values)
                    norm_cases += 1
                    literal = literal['parent_packet']
                units.audit_identity(literal['raw_parent'], literal, values)
                corrections += 1
                signed += not pos
    packet = build()
    source, out = polynomial_source(packet)
    encoded = compiler.encode_source(source)
    return dict(status='PASS_NEARY_WOODS_UNIVERSAL_JOINT_AND_UNITS', ledgers=records,
                complete_two_core_unit_corrections=corrections,
                complete_two_core_normalization_corrections=norm_cases,
                signed_cases=signed, fixed_recipe=constants_parent.u9.components()[-1],
                source_sha256=hashlib.sha256(json.dumps(encoded, sort_keys=True).encode()).hexdigest(),
                example=dict(source=encoded, output=out, comparisons=packet['comparisons'],
                         parameters=packet['parameters'], auxiliaries=packet['auxiliaries'],
                         fixed_numeral_definitions=compiler.NUMERALS),
                scope='Two native cores suffice after the proved recoder/history AND fusion. '
                      'The normalized complete U9 polynomial costs303=144M159A with51 '
                      'positive witnesses,16 comparisons and four program parameters. '
                      'Degree is conservatively propagated over the actual complete DAG. '
                      'Positive outer equivalence uses fresh canonical native auxiliaries; '
                      'no off-zero identity with the old unfused377 polynomial is asserted.')


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
