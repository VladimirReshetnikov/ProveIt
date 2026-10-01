"""Complete ordinary-input fixed-block binary-tag compiler.

Input duration is dyadic and independently quantified from tag-history
duration. Universal fixed-table instantiation is a separate obligation.
"""
import argparse
from collections import Counter
from functools import lru_cache
import hashlib
import json
from pathlib import Path
import random

import native_binary_dyadic_duration_recoder as recoder
import binary_tag_shared_counter_loader as boundary
import binary_tag_four_tile_history as tag
import gpcp_complete_fixed_program_units as units
import gpcp_normalized_strong_compiler as normalized
import pcp_affine_slope_class_history as selected

execute = tag.execute
scalar = tag.scalar


def input_blocks(beta, prefix, data0, data1, middle, mu, tail):
    words = dict(prefix=prefix, data0=data0, data1=data1, middle=middle, mu=mu, tail=tail)
    assert isinstance(beta, int) and beta >= 2
    assert all(set(word) <= set('bc') for word in words.values())
    assert data0 and data1 and mu and tail and tail[-1] == 'b'
    assert Counter(data0) == Counter(data1)
    encoded = {key: tag.encode(word, beta) for key, word in words.items()}
    encoded['tail'] = tag.endpoint(tail, beta)
    constants = boundary.constants(**encoded)
    m = constants['m']
    assert (len(prefix)+len(middle)+len(tail)-1) % (beta-1) == 0
    assert (len(data0)+m*len(mu)) % (beta-1) == 0
    return dict(words=words, constants=constants, beta=beta, counter_multiple=m)


def example_blocks(beta=3, reverse=False):
    assert beta in (2, 3, 4, 7)
    data0, data1 = ('cb', 'bc') if reverse else ('bc', 'cb')
    return input_blocks(beta, 'b'*(beta-2), data0, data1, 'b', 'c', 'b')


@lru_cache(None)
def tag_packet(beta, production):
    return tag.build(beta, production)


def build_raw(blocks=None, production='ccbbb', *, inline_initial=True, program_code=None):
    blocks = example_blocks() if blocks is None else blocks
    beta = blocks['beta']
    assert production and production[-1] == 'b' and set(production) <= set('bc')
    assert (len(production)-1) % (beta-1) == 0
    c = blocks['constants']
    if inline_initial:
        assert c['B'] >= 0, 'Use the supplied-positive endpoint for reversed data blocks.'
    left = recoder.build(c['D'])
    load = boundary.build(c, shared_modulus=True)
    right = tag_packet(beta, production)['raw_packet']
    program = []
    parameters = ['x']
    loaded = 'x'
    if program_code == 'parameter':
        parameters += ['program_code']
        program = [('program_twice', '+', 'x', 'x'),
                   ('program_odd', '+', 'program_twice', 1),
                   ('program_input', '*', 'program_code', 'program_odd')]
        loaded = 'program_input'
    elif program_code is not None:
        assert isinstance(program_code, int) and program_code > 0
        program = [('program_scaled', '*', 2*program_code, 'x'),
                   ('program_input', '+', 'program_scaled', program_code)]
        loaded = 'program_input'
    la = lambda value: loaded if value == 'x' else value
    def ba(value):
        if isinstance(value, int) or value in ('Q', 'z', 'modulus'):
            return value
        return 'load__'+value
    initial = 'load__tag_input' if inline_initial else 'tag_value'
    def ha(value):
        if isinstance(value, int):
            return value
        return initial if value == 'x' else 'hist__'+value
    source = program + [(n, op, la(a), la(b)) for n, op, a, b in left['source']]
    source += [(ba(n), op, ba(a), ba(b)) for n, op, a, b in load['source']]
    source += [(ha(n), op, ha(a), ha(b)) for n, op, a, b in right['source']]
    pairs = [(la(a), la(b)) for a, b in left['comparisons']]
    pairs += [(ba(a), ba(b)) for a, b in load['comparisons']]
    if not inline_initial:
        pairs += [('load__tag_input', 'tag_value')]
    front_count = len(pairs)
    pairs += [(ha(a), ha(b)) for a, b in right['comparisons']]
    aux = ['z']+left['auxiliaries']+['load__r']
    if not inline_initial:
        aux += ['tag_value']
    aux += [ha(n) for n in right['auxiliaries']]
    known = set(parameters+aux)
    assert len(known) == len(parameters)+len(aux)
    for n, op, a, b in source:
        assert n not in known and op in ('+', '-', '*')
        assert all(not isinstance(v, str) or v in known for v in (a, b))
        known.add(n)
    counts = Counter('M' if op == '*' else 'A' for _, op, _, _ in source)
    return dict(source=source, comparisons=pairs, parameters=parameters, auxiliaries=aux,
                operations=len(source), multiplications=counts['M'],
                additions_subtractions=counts['A'], equations=len(pairs), witnesses=len(aux),
                width=c['D'], beta=beta, production=production, blocks=blocks,
                inline_initial=inline_initial, program_code=program_code,
                loader_operations=len(program), loaded_input=loaded,
                initial_register=initial, boundary_comparisons=front_count,
                recoder_packet=left, loader_packet=load, tag_packet=right,
                history_packet=right['history_packet'], tiles=4,
                layout=right['history_packet']['layout'], form='raw')


def build(*args, form='normalized', **kwargs):
    assert form in ('raw', 'units', 'normalized')
    raw = build_raw(*args, **kwargs)
    if form == 'raw':
        return raw
    packet = units.rewrite(raw)
    packet.update(unit_product=True, form='units')
    if form == 'normalized':
        packet = normalized.rewrite(packet)
        packet['form'] = form
    return packet


def polynomial_source(packet):
    if packet['form'] == 'raw':
        return selected.parent.native.parent.sos_source(packet['source'], packet['comparisons'])
    return units.polynomial_source(packet)


def component_values(packet, values):
    assert packet['form'] == 'raw'
    env = execute(packet['source'], values)
    rv = {n: values[n] for n in packet['recoder_packet']['parameters']+packet['recoder_packet']['auxiliaries']}
    rv['x'] = env[packet['loaded_input']]
    bv = dict(Q=env['Q'], z=values['z'], modulus=env['modulus'], r=values['load__r'])
    hv = {n: values['hist__'+n] for n in packet['tag_packet']['auxiliaries']}
    hv['x'] = env[packet['initial_register']]
    return rv, bv, hv


def independent_raw(packet, values):
    rv, bv, hv = component_values(packet, values)
    residuals = recoder.independent(packet['recoder_packet'], rv)
    c = packet['blocks']['constants']
    residuals.append(c['L']*bv['r']-bv['modulus'])
    if not packet['inline_initial']:
        residuals.append(boundary.folded(c, bv['Q'], bv['z'], bv['r'])-values['tag_value'])
    hp = packet['history_packet']
    hvalues = {n: hv[n] for n in hp['auxiliaries']}
    hvalues.update(Vinitial=hv['x'], Ufinal=hv['Ufinal'],
                   Vfinal=(1 << (packet['beta']+1))*hv['Ufinal']+(1 << packet['beta']))
    residuals += selected.manual(hp, hvalues)[0]
    return residuals


def degree_audit(packet):
    """Literal upper degrees plus a nonzero top specialization, with checked norm cancellation."""
    names = packet['parameters']+packet['auxiliaries']
    degree = {name: 1 for name in names}
    top = {name: 1+i % 3 for i, name in enumerate(names)}
    for prefix in ('geo__', 'and__', 'hist__and__'):
        top[prefix+'tau_gap'] = 1
        top[prefix+'eta'] = top[prefix+'zeta'] = 1
    d = lambda value: degree[value] if isinstance(value, str) else 0
    c = lambda value: top[value] if isinstance(value, str) else value
    rows = {name: (op, a, b) for name, op, a, b in packet['source']}
    overrides = {} if packet['form'] == 'raw' else {
        prefix+'R15': prefix for prefix in ('geo__', 'and__', 'hist__and__')}
    for name, op, a, b in packet['source']:
        da, db = d(a), d(b)
        if op == '*':
            degree[name], top[name] = da+db, c(a)*c(b)
        else:
            degree[name] = max(da, db)
            ca = c(a) if da == degree[name] else 0
            cb = c(b) if db == degree[name] else 0
            top[name] = ca+cb if op == '+' else ca-cb
        if name in overrides:
            p = overrides[name]
            X, ac, G, aa, cc = (p+x for x in ('wn2', 'cam2', 'gam', 'R12', 'R10a'))
            expected = {p+'R15': ('-', p+'L15', p+'Ac2'),
                p+'R14': ('+', p+'D1', G), p+'D1': ('+', X, ac),
                ac: ('*', cc, aa), G: ('*', p+'ga', p+'a4m5'),
                p+'a4m5': ('+', p+'a4', 3), p+'a4': ('*', 4, aa),
                p+'A': ('+', p+'a_square', p+'a4m5'), p+'a_square': ('*', aa, aa),
                p+'c2': ('*', cc, cc), p+'Ac2': ('*', p+'A', p+'c2'),
                p+'L15': ('*', p+'R14', p+'R14')}
            assert all(rows[n] == row for n, row in expected.items())
            high = d(ac)+d(G)
            assert high > max(2*d(X), d(X)+d(ac), d(X)+d(G), 2*d(G), d(p+'a4m5')+2*d(cc))
            degree[name], top[name] = high, 2*c(ac)*c(G)
    pairs = packet['comparisons'] if packet['form'] == 'raw' else packet['comparisons'][:-1]
    residuals = []
    for a, b in pairs:
        high = max(d(a), d(b))
        coefficient = (c(a) if d(a) == high else 0)-(c(b) if d(b) == high else 0)
        residuals.append((a, b, high, coefficient))
    maximum = max(row[2] for row in residuals)
    coefficient = sum(row[3]**2 for row in residuals if row[2] == maximum)
    assert coefficient > 0
    unit_degree = 0
    if packet['form'] != 'raw':
        unit_degree = d(packet['unit_register'])
        coefficient *= c(packet['unit_register'])
    assert coefficient
    k = packet['width']
    N = packet['history_packet']['scale_exponent']
    e = 2 if packet['program_code'] == 'parameter' else 1
    if packet['form'] == 'raw':
        nu = k+2 if packet['inline_initial'] else 2
        expected_degree = max(12*k+40, 12*N*nu+16)
    else:
        nu = k*e+2 if packet['inline_initial'] else 2
        v, dd = (2*k+1)*e+1, N*nu
        assert d('and__q') == v and d('hist__and__q') == dd
        if packet['form'] == 'units':
            assert unit_degree == 14*e+19*v+2*k*e+20*dd-6*nu+64
            assert maximum == 4*max(v, dd)+10
        else:
            assert unit_degree == 30*e+35*v+2*k*e+36*dd-6*nu+142
            assert maximum == max(3*v+k*e+1, 4*dd-3*nu+1)
        expected_degree = unit_degree+2*maximum
    assert unit_degree+2*maximum == expected_degree
    blob = abs(coefficient).to_bytes((abs(coefficient).bit_length()+7)//8, 'big')
    return dict(exact_degree=unit_degree+2*maximum, unit_degree=unit_degree,
                maximum_residual_degree=maximum,
                factor_degrees={n: d(n) for n in packet.get('unit_factors', [])},
                highest_residuals=[[a, b, deg] for a, b, deg, _ in residuals if deg == maximum],
                leading_sign=1 if coefficient > 0 else -1,
                leading_sha256=hashlib.sha256(blob).hexdigest(),
                history_scale_exponent=N, history_length_degree=nu,
                loaded_input_degree=e)


def ledger(packet):
    source, _ = polynomial_source(packet)
    counts = Counter('M' if op == '*' else 'A' for _, op, _, _ in source)
    assert len(source) == packet['operations']+3*packet['equations']-1
    return dict(form=packet['form'], width=packet['width'], beta=packet['beta'],
                inline_initial=packet['inline_initial'], program_code=packet['program_code'],
                certificate=dict(operations=packet['operations'], multiplications=packet['multiplications'],
                    additions_subtractions=packet['additions_subtractions'],
                    equations=packet['equations'], witnesses=packet['witnesses']),
                polynomial=dict(operations=len(source), multiplications=counts['M'],
                    additions_subtractions=counts['A']), degree=degree_audit(packet))


def polynomial_degree_check(packet):
    """Evaluate actual factor/residual polynomials without the large final product."""
    import sympy as sp
    variable = sp.Symbol('T')
    names = packet['parameters']+packet['auxiliaries']
    weights = {name: 1+i % 3 for i, name in enumerate(names)}
    for prefix in ('geo__', 'and__', 'hist__and__'):
        weights[prefix+'tau_gap'] = 1
        weights[prefix+'eta'] = weights[prefix+'zeta'] = 1
    values = {n: sp.Poly(weights[n]*variable+i+1, variable) for i, n in enumerate(names)}
    source = [row for row in packet['source'] if not (
        row[0].startswith('complete_unit_product') or row[0].endswith('normalized_all_units'))]
    env = execute(source, values)
    pairs = packet['comparisons'] if packet['form'] == 'raw' else packet['comparisons'][:-1]
    residuals = [sp.Poly(scalar(a, env)-scalar(b, env), variable) for a, b in pairs]
    maximum = max(r.degree() for r in residuals)
    expected = degree_audit(packet)
    assert maximum == expected['maximum_residual_degree']
    coefficient = sum(r.LC()**2 for r in residuals if r.degree() == maximum)
    factors = [sp.Poly(env[n], variable) for n in packet.get('unit_factors', [])]
    assert {n: f.degree() for n, f in zip(packet.get('unit_factors', []), factors)} == expected['factor_degrees']
    for factor in factors:
        coefficient *= factor.LC()
    coefficient = int(coefficient)
    assert sum(f.degree() for f in factors)+2*maximum == expected['exact_degree']
    blob = abs(coefficient).to_bytes((abs(coefficient).bit_length()+7)//8, 'big')
    assert hashlib.sha256(blob).hexdigest() == expected['leading_sha256']
    return dict(form=packet['form'], inline_initial=packet['inline_initial'],
                program_code=packet['program_code'], exact_degree=expected['exact_degree'],
                leading_sha256=expected['leading_sha256'])


def audit_identity(packet, values):
    if packet['form'] == 'raw':
        source, out = polynomial_source(packet)
        env = execute(source, values)
        expected = independent_raw(packet, values)
        assert [scalar(a, env)-scalar(b, env) for a, b in packet['comparisons']] == expected
        assert env[out] == sum(v*v for v in expected)
    elif packet['form'] == 'units':
        units.audit_identity(packet, values)
    else:
        normalized.audit_identity(packet, values)
        units.audit_identity(packet['parent_packet'], normalized.lift(packet, values))


def initial_word(packet, bits):
    w = packet['blocks']['words']
    return (w['prefix']+''.join(w['data1'] if bit == '1' else w['data0'] for bit in bits)
            +w['middle']+w['mu']*(packet['blocks']['counter_multiple']*len(bits))+w['tail'])


def verify():
    rng = random.Random(3962026)
    records = []
    cases = signed = 0
    for beta in (2, 3, 4, 7):
      production = 'c'*(beta-1)+'b'*beta
      for inline in (True, False):
       for code in (None, 4, 'parameter'):
        for form in ('raw', 'units', 'normalized'):
            packet = build(example_blocks(beta), production, inline_initial=inline,
                           program_code=code, form=form)
            records.append(ledger(packet))
            for case in range(8):
                values = {n: rng.randrange(1, 4) if case < 4 else rng.randrange(-2, 3)
                          for n in packet['parameters']+packet['auxiliaries']}
                audit_identity(packet, values)
                cases += 1
                signed += case >= 4
    reversed_packet = build(example_blocks(3, True), inline_initial=False)
    records.append(ledger(reversed_packet))
    rejected = False
    try:
        build(example_blocks(3, True))
    except AssertionError:
        rejected = True
    assert rejected
    frames = runs = halts = 0
    for beta in (2, 3, 4, 7):
        packet = build(example_blocks(beta), 'c'*(beta-1)+'b'*beta, form='raw')
        c = packet['blocks']['constants']
        for n in (2, 4, 8):
            for x in sorted({1, 2, 3, (1 << n)-1}):
                bits = format(x, f'0{n}b')
                rv = recoder.outer_fixture(x, n, c['D'])
                Q = rv['q']**c['D']
                word = initial_word(packet, bits)
                assert len(word) >= beta and (len(word)-1) % (beta-1) == 0 and word[-1] == 'b'
                r = (Q-1)//c['L']
                assert boundary.folded(c, Q, rv['z'], r) == tag.sentinel(tag.endpoint(word, beta))
                values = {key: 1 for key in packet['parameters']+packet['auxiliaries']}
                values.update(rv, load__r=r)
                env = execute(packet['source'], values)
                assert env['load__tag_input'] == tag.sentinel(tag.endpoint(word, beta))
                assert all(scalar(a, env) == scalar(b, env) for a, b in
                           packet['comparisons'][:5]+packet['comparisons'][36:37])
                frames += 1
                result = tag.encode_halting_trace(word, beta, packet['production'], limit=100)
                runs += 1
                if result is not None:
                    selection, _ = result
                    assert selection and tag.decode_solution(word, beta, packet['production'], selection) == 'b'
                    fixture = selected.positive_outer_fixture(packet['history_packet'], selection,
                                                             env['load__tag_input'])
                    values.update({'hist__'+key: fixture[key] for key in packet['tag_packet']['auxiliaries']})
                    env = execute(packet['source'], values)
                    assert env['hist__tag_terminal'] == fixture['Vfinal']
                    assert all(scalar(a, env) == scalar(b, env) for a, b in
                               packet['comparisons'][packet['boundary_comparisons']:][:3])
                    halts += 1
    example = build()
    source, out = polynomial_source(example)
    exact = [polynomial_degree_check(build(example_blocks(2), 'cbb', form='raw')),
             polynomial_degree_check(build(example_blocks(3), inline_initial=False,
                                           program_code='parameter', form='normalized'))]
    return dict(status='PASS_BINARY_TAG_COMPLETE_DYADIC_COMPILER', ledgers=records,
                complete_output_identities=cases, signed_cases=signed,
                literal_framed_inputs=frames, bounded_tag_runs=runs, halting_outer_compositions=halts,
                reversed_inline_rejected=rejected,
                actual_factor_and_residual_polynomial_checks=exact,
                example=dict(ledger=ledger(example), parameters=example['parameters'],
                    auxiliaries=example['auxiliaries'], source=source,
                    comparisons=example['comparisons'], output=out),
                scope='Complete fixed-word-family tag halting predicate on ordinary positive input, '
                      'with an existential dyadic input duration and independent positive history duration. '
                      'A fixed universal machine/table is not instantiated. No below87 claim.',
                full_native_Pell_zeros_materialized=False)


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
    print(result['example']['ledger'])
