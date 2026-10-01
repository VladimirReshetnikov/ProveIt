"""Define the recoder scale through its positive loader repunit.

Soundness has an unconditional positive lift to the parent. Completeness
uses sufficiently long valid-program input padding, not a bijection of
all supplied parent zeros or arbitrary program-parameter relations.
"""
import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path
import random

import neary_woods_universal_positive_scale_partitions as parent

compiler = parent.compiler
units = parent.partitions.parent
sort_source = units.units.sort_source
execute = compiler.parent.execute
EXPECTED = [(288, 3980, 48), (289, 3486, 48), (290, 3440, 48),
            (291, 2322, 49), (292, 1554, 49), (293, 1508, 49),
            (294, 1142, 49), (295, 1098, 49), (296, 766, 49),
            (297, 734, 49), (298, 608, 49)]


def rewrite(old):
    assert not old.get('loader_defined_scale')
    compiler.check_source(old)
    nodes = {n: (op, a, b) for n, op, a, b in old['source']}
    kappa = nodes['load__repunit_product'][1]
    assert kappa == compiler.Numeral('repunit_divisor')
    expected = {
        'input_bound': ('+', 'x', 'input_slack'),
        'joined_scale_floor': ('+', 'input_bound', 'z'),
        'Q': ('+', 'joined_scale_floor', 'power_gap'),
        'modulus': ('-', 'Q', 1),
        'load__repunit_product': ('*', kappa, 'load__r'),
    }
    assert all(nodes[n] == row for n, row in expected.items())
    removed = ('load__repunit_product', 'modulus')
    assert old['comparisons'].count(removed) == 1
    consumers = lambda n: {v for v, _, a, b in old['source'] if n in (a, b)}
    assert consumers('load__repunit_product') == set()
    assert consumers('power_gap') == {'Q'}
    assert [pair for pair in old['comparisons'] if 'load__repunit_product' in pair] == [removed]
    assert all('power_gap' not in pair for pair in old['comparisons'])
    assert 'load__r' in old['auxiliaries'] and 'load__r' not in old['parameters']
    dependencies = {n: {n} for n in old['parameters']+old['auxiliaries']}
    dep = lambda n: dependencies[n] if isinstance(n, str) else set()
    for n, _, a, b in old['source']:
        dependencies[n] = dep(a) | dep(b)
    assert not {'power_gap', 'load__r'} & dep('joined_scale_floor')
    source = [row for row in old['source'] if row[0] not in
              {'Q', 'modulus', 'load__repunit_product'}]
    source += [('load__r', '+', 'joined_scale_floor', 'power_gap'),
               ('modulus', '*', kappa, 'load__r'), ('Q', '+', 'modulus', 1)]
    auxiliaries = [n for n in old['auxiliaries'] if n != 'load__r']
    source = sort_source(source, old['parameters']+auxiliaries)
    comparisons = [p for p in old['comparisons'] if p != removed]
    count = Counter('M' if op == '*' else 'A' for _, op, _, _ in source)
    packet = dict(old, source=source, comparisons=comparisons, auxiliaries=auxiliaries,
                  operations=len(source), multiplications=count['M'], additions_subtractions=count['A'],
                  equations=len(comparisons), witnesses=len(auxiliaries), loader_defined_scale=True,
                  loader_parent=old, loader_removed_comparison=removed,
                  loader_completeness_scope='Valid program slices with sufficiently long dyadic leading-zero padding.')
    assert count == Counter('M' if op == '*' else 'A' for _, op, _, _ in old['source'])
    assert len(source) == old['operations'] and packet['equations'] == old['equations']-1
    assert packet['witnesses'] == old['witnesses']-1
    compiler.check_source(packet)
    return packet


def build(operations=288, *, merge_bound=True, witnesses=None):
    assert witnesses in (None, 48, 49, 50)
    old = parent.build(operations+3, merge_bound=merge_bound,
                       witnesses=None if witnesses is None else witnesses+1)
    return rewrite(old)


def polynomial_source(packet):
    source = list(packet['source'])
    anchored = packet['unit_product']
    if anchored:
        assert packet['comparisons'][-1] == (packet['unit_register'], 1)
    pairs = packet['comparisons'][:-1] if anchored else packet['comparisons']
    last = None
    for i, (a, b) in enumerate(pairs):
        r, square = f'loader_residual_{i}', f'loader_square_{i}'
        source += [(r, '-', a, b), (square, '*', r, r)]
        if last is None:
            last = square
        else:
            n = f'loader_sum_{i}'
            source.append((n, '+', last, square))
            last = n
    assert last is not None
    if anchored:
        source += [('loader_positive', '+', last, 1),
                   ('loader_scaled', '*', packet['unit_register'], 'loader_positive'),
                   ('loader_output', '-', 'loader_scaled', 1)]
        last = 'loader_output'
    assert len(source) == packet['operations']+3*packet['equations']-1
    return source, last


def degree_bound(packet):
    # The frozen core degree propagator checks the literal main-norm
    # cancellation. For SOS include every group residual before its dummy
    # final unit comparison; the dummy contributes no degree or source gate.
    context = packet if packet['unit_product'] else dict(packet,
        comparisons=packet['comparisons']+[(0, 0)], unit_register=None)
    return units.degree_bound(context)


def ledger(packet):
    source, output = polynomial_source(packet)
    count = Counter('M' if op == '*' else 'A' for _, op, _, _ in source)
    bound = degree_bound(packet)
    old = packet['loader_parent']
    assert bound == degree_bound(old)
    assert bound['degree_upper_bound'] == old['positive_scale_partition_record']['polynomial']['degree_upper_bound']
    return dict(certificate={n: packet[n] for n in ('operations', 'multiplications',
        'additions_subtractions', 'equations', 'witnesses')},
        polynomial=dict(operations=len(source), multiplications=count['M'], additions_subtractions=count['A'],
                        degree_upper_bound=bound['degree_upper_bound'], exact_degree_claimed=False),
        bound_is_program_E=packet['bound_is_program_E'], parameters=packet['parameters'],
        factor_partition=packet['factor_partition'], partition_anchor=packet['partition_anchor'],
        group_degree_bounds=old['positive_scale_partition_record']['group_degree_bounds'],
        output=output)


def lift_to_parent(packet, values):
    env = execute(packet['source'], values)
    return dict(values, **{'load__r': env['load__r'],
                         'power_gap': env['Q']-env['joined_scale_floor']})


def project_from_parent(packet, values):
    old = packet['loader_parent']
    env = execute(old['source'], values)
    result = {n: v for n, v in values.items() if n != 'load__r'}
    result['power_gap'] = values['load__r']-env['joined_scale_floor']
    return result


def source_closure(source, output):
    nodes = {n: (a, b) for n, _, a, b in source}
    needed = set()
    def visit(n):
        if not isinstance(n, str) or n not in nodes or n in needed:
            return
        needed.add(n)
        for v in nodes[n]:
            visit(v)
    visit(output)
    assert len(nodes) == len(source) and needed == set(nodes)


def audit(packet, seed):
    rng = random.Random(seed)
    old_template, old_output = parent.polynomial_source(packet['loader_parent'])
    for case in range(32):
        positive = case < 16
        draw = lambda: rng.randrange(1, 7) if positive else rng.randrange(-4, 5)
        numerals = {n: draw() for n in compiler.NUMERALS}
        if positive:
            numerals.update(recoder_radix=4, repunit_divisor=7)
        literal = units.constants_parent.materialize_packet(packet, numerals)
        values = {n: draw() for n in literal['parameters']+literal['auxiliaries']}
        restored = lift_to_parent(literal, values)
        source, output = polynomial_source(literal)
        old = literal['loader_parent']
        old_source = compiler.materialize(old_template, numerals)
        env, before = execute(source, values), execute(old_source, restored)
        assert all(env[n] == before[n] for n, _, _, _ in old['source'] if n != 'load__repunit_product')
        assert before['load__repunit_product'] == before['modulus']
        assert env[output] == before[old_output]
        assert project_from_parent(literal, restored) == values
        if positive:
            assert min(restored.values()) > 0
    return dict(whole_output_identities=32, signed_cases=16,
                positive_forward_lifts=16, coordinate_round_trips=32)


def padding_audit():
    count = 0
    for D in (2, 3, 4, 7):
        radix = 1 << D
        for n in (4, 8, 16):
            for x in list(range(1, min(1 << (n-1), 65)))+[ (1 << (n-1))-1 ]:
                assert x.bit_length() < n
                q, Q = 1 << n, 1 << (D*n)
                z = sum(((x >> i) & 1)*(radix**i) for i in range(x.bit_length()))
                repunit = (Q-1)//(radix-1)
                b = repunit-q-z
                assert repunit-z >= radix**(n-1) > q
                assert b > 0 and (radix-1)*(q+z+b)+1 == Q
                count += 1
    # A genuine typed recoder point need not admit the inverse coordinate.
    # This is not a full universal-polynomial zero or a claim about an
    # invalid program slice. Padding, rather than a tuple bijection, is used.
    D, n, x = 3, 2, 3
    q, Q, z, repunit = 4, 64, 9, 9
    assert Q == 1 << (D*n) and z == sum(((x >> i) & 1)*(1 << (D*i)) for i in range(n))
    assert (Q-1)//((1 << D)-1) == repunit
    assert Q-q-z > 0 and repunit-q-z == -4
    return dict(typed_padded_recoder_cases=count,
        nonpositive_inverse_recoder_example=dict(D=D,n=n,x=x,q=q,Q=Q,z=z,repunit=repunit,
                                                 old_power_gap=Q-q-z,new_power_gap=-4),
        scope='Exact recoder/loader values and padding inequalities, not materialized native Pell zeros.')


def verify():
    records = []
    for interface in (False, True):
        for operations, degree, witnesses in EXPECTED:
            packet = build(operations, merge_bound=interface)
            rec = ledger(packet)
            assert rec['polynomial']['operations'] == operations
            assert rec['polynomial']['degree_upper_bound'] == degree
            assert packet['witnesses'] == witnesses
            rec['audit'] = audit(packet, 288298+len(records))
            source, output = polynomial_source(packet)
            source_closure(source, output)
            encoded = compiler.encode_source(source)
            rec.update(source=encoded, auxiliaries=packet['auxiliaries'],
                source_sha256=hashlib.sha256(json.dumps(encoded, sort_keys=True).encode()).hexdigest())
            records.append(rec)
    # A fixed48-witness alternative outside the unrestricted degree frontier.
    restricted = []
    for interface in (False, True):
        packet = build(295, merge_bound=interface, witnesses=48)
        rec = ledger(packet)
        assert rec['polynomial']['degree_upper_bound'] == 1344
        rec['audit'] = audit(packet, 288488+interface)
        source, output = polynomial_source(packet)
        source_closure(source, output)
        rec.update(source=compiler.encode_source(source), auxiliaries=packet['auxiliaries'])
        restricted.append(rec)
    return dict(status='PASS_NEARY_WOODS_UNIVERSAL_LOADER_SCALE288',
        frontier=EXPECTED, ledgers=records, fixed48_degree1344=restricted,
        whole_output_identities=32*(len(records)+len(restricted)),
        signed_cases=16*(len(records)+len(restricted)), padding=padding_audit(),
        scope='Complete universal ordinary-input representation on the inherited valid U9 program slices. '
              'Positive sound lift on all supplied tuples; completeness uses sufficiently long dyadic '
              'leading-zero padding. No bijection of all positive parent zeros or equivalence on arbitrary '
              'invalid program parameters is asserted. Degrees are upper bounds; separate75/87 unchanged.')


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
    print(result['frontier'])
