"""Complete ordinary-input U9 tag polynomial with population-certified width.

The actual fixed U9 table is unchanged. Two paid gates and a positive gap
replace its enormous fixed-exponent power chain. Fixed numerals stay fixed.
"""
import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path
import random

import neary_woods_universal_u9_tag_chain as u9
import native_binary_population_width_recoder as population

compiler = u9.compiler
D = u9.D


def build(form='normalized', *, merge_bound=True):
    assert form in ('raw', 'units', 'normalized')
    table, counts, machine, summary, recipe = u9.components()
    packet = population.rewrite(compiler.raw_build(D, counts['beta'], counts['e_u_length']),
                                compiler.Numeral('repunit_divisor'))
    assert packet['source'][0] == ('program_duration_bound', '+', 'program_bound', 'program_duration_gap')
    if merge_bound:
        alias = lambda v: 'program_E' if v == 'program_bound' else v
        packet['source'] = [(n, op, alias(a), alias(b)) for n, op, a, b in packet['source']]
        packet['comparisons'] = [(alias(a), alias(b)) for a, b in packet['comparisons']]
        packet['parameters'] = [n for n in packet['parameters'] if n != 'program_bound']
    packet['bound_is_program_E'] = merge_bound
    if form != 'raw':
        packet = compiler.parent.units.rewrite(packet)
        packet.update(form='units', unit_product=True)
        if form == 'normalized':
            packet = compiler.parent.normalized.rewrite(packet)
            packet['form'] = form
    compiler.check_source(packet)
    rows = {n: (op, a, b) for n, op, a, b in packet['source']}
    assert rows['Q'] == ('+', 'q' if form == 'raw' else 'input_bound', 'power_gap')
    assert rows['geometry_index'] == ('*', compiler.Numeral('repunit_divisor'), 'J')
    assert rows['B'] == ('*', compiler.Numeral('recoder_radix'), 'Q')
    assert 'power_gap' in packet['auxiliaries']
    return packet


def degree_bound(packet):
    """Literal propagation, guarded main-norm cancellation, no coefficient expansion."""
    degrees = {n: 1 for n in packet['parameters']+packet['auxiliaries']}
    d = lambda v: degrees[v] if isinstance(v, str) else 0
    rows = {n: (op, a, b) for n, op, a, b in packet['source']}
    overrides = {} if packet['form'] == 'raw' else {
        p+'R15': p for p in ('geo__', 'and__', 'hist__and__')}
    for n, op, a, b in packet['source']:
        degrees[n] = d(a)+d(b) if op == '*' else max(d(a), d(b))
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
            degrees[n] = max(2*d(X), d(X)+d(ac), d(X)+d(G),
                             d(ac)+d(G), 2*d(G), d(p+'a4m5')+2*d(cc))
    raw = packet['form'] == 'raw'
    pairs = packet['comparisons'] if raw else packet['comparisons'][:-1]
    maximum = max(max(d(a), d(b)) for a, b in pairs)
    product = 0 if raw else d(packet['unit_register'])
    expected = {'raw': (0, 272, 544), 'units': (1012, 186, 1384),
                'normalized': (1874, 165, 2204)}[packet['form']]
    assert (product, maximum, product+2*maximum) == expected
    assert d('Q') == d('B') == d('geometry_index') == 1
    assert d('load__tag_input') == 3 and d('hist__and__q') == 44
    return dict(degree_upper_bound=product+2*maximum,
                unit_degree_bound=product, maximum_residual_degree_bound=maximum,
                native_scale_degrees=[d('Q'), d('and__q'), d('hist__and__q')],
                factor_degree_bounds={n: d(n) for n in packet.get('unit_factors', [])},
                exact_degree_claimed=False)


def ledger(packet):
    source, out = compiler.parent.polynomial_source(packet)
    counts = Counter('M' if op == '*' else 'A' for _, op, _, _ in source)
    expected = {'raw': (310, 56, 89, 477, 208, 269),
                'units': (319, 28, 70, 402, 189, 213),
                'normalized': (325, 25, 70, 399, 192, 207)}[packet['form']]
    assert (packet['operations'], packet['equations'], packet['witnesses'],
            len(source), counts['M'], counts['A']) == expected
    assert packet['parameters'] == [n for n in compiler.PARAMETERS
                                   if not (packet['bound_is_program_E'] and n == 'program_bound')]
    return dict(form=packet['form'], width=D, width_relation_operations=2,
        certificate={k: packet[k] for k in ('operations', 'multiplications',
                     'additions_subtractions', 'equations', 'witnesses')},
        polynomial=dict(operations=len(source), multiplications=counts['M'],
                        additions_subtractions=counts['A'], output=out),
        parameters=packet['parameters'], bound_is_program_E=packet['bound_is_program_E'],
        **degree_bound(packet))


def materialize_packet(packet, constants):
    """Finite algebra specializations, not the enormous actual fixed numerals."""
    memo = {}
    def visit(value):
        if isinstance(value, compiler.Numeral):
            return constants[value.name]
        if not isinstance(value, (dict, list, tuple)):
            return value
        key = id(value)
        if key in memo:
            return memo[key]
        if isinstance(value, dict):
            result = {}
            memo[key] = result
            result.update((k, visit(v)) for k, v in value.items())
        elif isinstance(value, list):
            result = []
            memo[key] = result
            result.extend(visit(v) for v in value)
        else:
            result = tuple(visit(v) for v in value)
            memo[key] = result
        return result
    return visit(packet)


def independent_raw(packet, values, constants):
    """Assemble recoder, changed geometry, loader and untouched history separately."""
    q, P, J, K, Ahat, z = (values[n] for n in ('q', 'P', 'J', 'K', 'Ahat', 'z'))
    n = values['program_E' if packet['bound_is_program_E'] else 'program_bound']+values['program_duration_gap']
    Q = q+values['power_gap']
    B = constants['recoder_radix']*Q
    r = constants['repunit_divisor']*J
    S, H = q*P, values['x']*J
    rr = [(B-1)*J+1-P, (2*B-1)*K+1-S,
          values['x']+values['input_slack']-q,
          Ahat+Q-(Q-1)*values['quotient_hat']-z-2,
          z+values['output_slack']-Q]
    geometry = population.parent.geometry.build(shared_B=True)
    gv = {name: values['geo__'+name] for name in geometry['auxiliaries']}
    gv.update(q=Q, J=r)
    rr += population.parent.geometry.manual(gv, B)
    source, pairs, _ = population.parent.masked.source('and64_prescribed')
    _, aux = population.parent.masked.domains('and64_prescribed')
    av = {name: values['and__'+name] for name in aux}
    av.update(P=B*S, Hhat=B*H+n+1, Mhat=B*K+n, Zhat=B*(Ahat-1)+1)
    env = population.parent.masked.parent.execute(source, av)
    rr += [env[a]-env[b] for a, b in pairs]
    rr += [(B-1)*values['duration_quotient']+n-J,
           n+values['duration_slack']-(B-1)]
    lr = values['load__r']
    rr += [constants['repunit_divisor']*lr-(Q-1)]
    Vi = (values['program_A']*lr+values['program_B']*z)*Q+values['program_T']*lr+values['program_E']
    h = packet['history_packet']
    hv = {name: values['hist__'+name] for name in h['auxiliaries']}
    hv.update(Ufinal=values['hist__Ufinal'], Vinitial=Vi,
              Vfinal=constants['terminal_scale']*values['hist__Ufinal']+constants['terminal_offset'])
    hs = compiler.materialize(h['source'], constants)
    he = compiler.parent.execute(hs, hv)
    rr += [compiler.parent.scalar(a, he)-compiler.parent.scalar(b, he) for a, b in h['comparisons']]
    assert len(rr) == 56
    return rr


def verify():
    rng = random.Random(399192207)
    records = []
    raw_cases = corrections = signed = 0
    for merge_bound in (False, True):
        for form in ('raw', 'units', 'normalized'):
            packet = build(form, merge_bound=merge_bound)
            records.append(ledger(packet))
            constants = {n: rng.randrange(-7, 8) for n in compiler.NUMERALS}
            literal = materialize_packet(packet, constants)
            for case in range(64):
                values = {n: rng.randrange(1, 5) if case < 32 else rng.randrange(-3, 4)
                          for n in packet['parameters']+packet['auxiliaries']}
                if form == 'raw':
                    expected = independent_raw(packet, values, constants)
                    source, out = compiler.parent.polynomial_source(literal)
                    env = compiler.parent.execute(source, values)
                    rr = [compiler.parent.scalar(a, env)-compiler.parent.scalar(b, env)
                          for a, b in literal['comparisons']]
                    assert rr == expected and env[out] == sum(r*r for r in expected)
                    raw_cases += 1
                elif form == 'units':
                    compiler.parent.units.audit_identity(literal, values)
                    corrections += 1
                else:
                    compiler.parent.normalized.audit_identity(literal, values)
                    lifted = compiler.parent.normalized.lift(literal, values)
                    compiler.parent.units.audit_identity(literal['parent_packet'], lifted)
                    corrections += 1
                signed += case >= 32
    # Original U9 fixed table/word contract, with the new geometry port.
    table, counts, machine, summary, recipe = u9.components()
    assert D == 128*table['z']*counts['bit_block_length']
    assert counts['beta'] == 1182020 and table['Q'] == 1968
    assert ''.join(u9.u15.production_letter(table, counts, j) for j in range(3)) == 'bcb'
    assert u9.u15.production_letter(table, counts, counts['u_length']-1) == 'b'
    packet = build()
    source, out = compiler.parent.polynomial_source(packet)
    encoded = compiler.encode_source(source)
    return dict(status='PASS_NEARY_WOODS_UNIVERSAL_POPULATION_TAG',
        fixed_recipe=recipe, actual_machine=machine, cts=summary, tag_counts=counts,
        ledgers=records, independent_complete_raw_residual_and_SOS_cases=raw_cases,
        complete_unit_and_normalization_correction_cases=corrections, signed_cases=signed,
        source_sha256=hashlib.sha256(json.dumps(encoded, sort_keys=True).encode()).hexdigest(),
        example=dict(source=encoded, output=out, comparisons=packet['comparisons'],
                     parameters=packet['parameters'], auxiliaries=packet['auxiliaries'],
                     fixed_numeral_definitions=compiler.NUMERALS),
        scope='One explicit U9-derived universal polynomial:399 operations,70 positive '
              'witnesses,four positive program parameters,degree at most2204. Two paid '
              'population-width gates replace the fixed-exponent chain. Geometry is '
              'reconstructed at scale Q and index(2^D-1)J; no same-raw-polynomial identity '
              'or all-witness bijection is asserted. All huge fixed numerals retain exact '
              'recipes; no expanded universal word or full numerical native Pell zero.')


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
