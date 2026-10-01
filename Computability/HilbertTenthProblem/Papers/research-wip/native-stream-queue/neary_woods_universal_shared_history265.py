"""Reuse paid history powers and selector prefixes in the complete U9 source.

Three local identities save one multiplication, one multiplication/addition,
and one addition. Every complete polynomial and supplied coordinate is unchanged.
"""
import argparse
from collections import Counter
import copy
import hashlib
import json
from pathlib import Path
import random

import neary_woods_universal_computed_ports_partitions as parent

compiler = parent.compiler
execute = parent.execute
sort_source = parent.loader.sort_source
leaves = parent.factored.leaves
polynomial_source = parent.polynomial_source
degree_bound = parent.degree_bound
OPTIONS = ((True, False, False), (False, True, False), (False, False, True),
           (True, True, False), (True, False, True), (False, True, True), (True, True, True))


def rewrite(old, *, repunit=True, selectors=True, radix=True):
    assert all(isinstance(v, bool) for v in (repunit, selectors, radix))
    assert repunit or selectors or radix
    assert not old.get('shared_history_reuse')
    compiler.check_source(old)
    rows = {n: (op, a, b) for n, op, a, b in old['source']}
    P, P2 = 'hist__P__10', 'hist__P2__51'
    assert rows[P2] == ('*', P, P)
    expected, additions, retained = {}, [], set()
    if repunit:
        expected.update({
            'hist__repunit_factor__50': ('+', P, 1),
            'hist__repunit_factor__52': ('+', P2, 1),
            'hist__repunit_product__53': ('*', 'hist__repunit_factor__50', 'hist__repunit_factor__52'),
            'hist__repunit_tail__64': ('+', P2, 'hist__repunit_factor__50'),
            'hist__P3__78': ('*', P2, P),
        })
        additions.append(('hist__repunit_product__53', '+',
                          'hist__P3__78', 'hist__repunit_tail__64'))
        retained.add('hist__repunit_product__53')
    if selectors:
        expected.update({
            'hist__pack_product__44': ('*', P, 'hist__Shat3'),
            'hist__pack_sum__45': ('+', 'hist__Shat2', 'hist__pack_product__44'),
            'hist__pack_product__46': ('*', P, 'hist__pack_sum__45'),
            'hist__pack_sum__47': ('+', 'hist__Shat1', 'hist__pack_product__46'),
            'hist__pack_product__48': ('*', P, 'hist__pack_sum__47'),
            'hist__pack_sum__49': ('+', 'hist__Shat0', 'hist__pack_product__48'),
            'hist__pack_product__60': ('*', P, 'hist__Shat1'),
            'hist__pack_sum__61': ('+', 'hist__Shat0', 'hist__pack_product__60'),
        })
        additions += [('shared_history_selector_high', '*', P2, 'hist__pack_sum__45'),
                      ('hist__pack_sum__49', '+', 'hist__pack_sum__61', 'shared_history_selector_high')]
        retained.add('hist__pack_sum__49')
    if radix:
        expected.update({'Bm1': ('-', 'B', 1), 'twiceB': ('+', 'B', 'B'),
                         'twiceBm1': ('-', 'twiceB', 1)})
        additions.append(('twiceBm1', '+', 'B', 'Bm1'))
        retained.add('twiceBm1')
    assert all(rows[n] == row for n, row in expected.items())
    erased = set()
    if repunit:
        erased.add('hist__repunit_factor__52')
    if selectors:
        erased |= {'hist__pack_product__46', 'hist__pack_sum__47', 'hist__pack_product__48'}
    if radix:
        erased.add('twiceB')
    replaced = erased | retained
    assert not erased & set(old['parameters']+old['auxiliaries'])
    for key in ('comparisons', 'unit_factors', 'group_products', 'interfaces',
                'public_registers', 'fusion_interfaces', 'projected_coordinates'):
        assert not erased & leaves(old.get(key, {})), key
    assert all(n in replaced or not erased & {a, b}
               for n, _, a, b in old['source'])
    fresh = {n for n, _, _, _ in additions}-retained
    assert not fresh & (set(rows) | set(old['parameters']+old['auxiliaries']))
    source = [row for row in old['source'] if row[0] not in replaced]+additions
    source = sort_source(source, old['parameters']+old['auxiliaries'])
    counts = Counter('M' if op == '*' else 'A' for _, op, _, _ in source)
    saving = int(repunit)+2*int(selectors)+int(radix)
    packet = dict(old, source=source, operations=len(source),
        multiplications=counts['M'], additions_subtractions=counts['A'],
        shared_history_reuse=True, shared_history_parent=old,
        shared_history_options=dict(repunit=repunit, selectors=selectors, radix=radix),
        shared_history_erased_registers=sorted(erased), shared_history_saving=saving,
        identical_complete_polynomial=True, identical_positive_coordinates=True)
    assert counts['M'] == old['multiplications']-int(repunit)-int(selectors)
    assert counts['A'] == old['additions_subtractions']-int(selectors)-int(radix)
    assert len(source) == old['operations']-saving
    compiler.check_source(packet)
    return packet


def build(operations=None, *, merge_bound=True, witnesses=None, repunit=True, selectors=True, radix=True):
    saving = int(repunit)+2*int(selectors)+int(radix)
    cost = 269 if operations is None else operations+saving
    return rewrite(parent.build_factored(cost,
        merge_bound=merge_bound, witnesses=witnesses), repunit=repunit, selectors=selectors, radix=radix)


def restore_parent_registers(packet, env):
    result = {}
    if packet['shared_history_options']['repunit']:
        result['hist__repunit_factor__52'] = env['hist__P2__51']+1
    if packet['shared_history_options']['selectors']:
        p46 = env['hist__P__10']*env['hist__pack_sum__45']
        s47 = env['hist__Shat1']+p46
        result.update(hist__pack_product__46=p46, hist__pack_sum__47=s47,
                      hist__pack_product__48=env['hist__P__10']*s47)
    if packet['shared_history_options']['radix']:
        result['twiceB'] = env['B']+env['B']
    assert set(result) == set(packet['shared_history_erased_registers'])
    return result


def ledger(packet):
    old = packet['shared_history_parent']
    source, output = polynomial_source(packet)
    before, _ = polynomial_source(old)
    c = Counter('M' if op == '*' else 'A' for _, op, _, _ in source)
    bound = degree_bound(packet)
    assert bound == degree_bound(old)
    assert len(source) == len(before)-packet['shared_history_saving']
    assert packet['parameters'] == old['parameters'] and packet['auxiliaries'] == old['auxiliaries']
    assert packet['comparisons'] == old['comparisons']
    parent.loader.source_closure(source, output)
    return dict(options=packet['shared_history_options'],
        normalized_prefixes=packet['normalized_prefixes'],
        positive_scale_prefixes=packet.get('positive_scale_prefixes', ()),
        bound_is_program_E=packet['bound_is_program_E'],
        certificate={k: packet[k] for k in ('operations', 'multiplications',
            'additions_subtractions', 'equations', 'witnesses')},
        polynomial=dict(operations=len(source), multiplications=c['M'], additions_subtractions=c['A'],
            degree_upper_bound=bound['degree_upper_bound'], exact_degree_claimed=False),
        factor_partition=packet['factor_partition'], partition_anchor=packet['partition_anchor'],
        output=output)


def audit(packet, seed, cases=16):
    rng = random.Random(seed)
    old = packet['shared_history_parent']
    old_source, old_output = polynomial_source(old)
    new_source, new_output = polynomial_source(packet)
    for case in range(cases):
        draw = lambda: rng.randrange(1, 5) if case < cases//2 else rng.randrange(-3, 4)
        constants = {n: draw() for n in compiler.NUMERALS}
        values = {n: draw() for n in packet['parameters']+packet['auxiliaries']}
        before = execute(compiler.materialize(old_source, constants), values)
        after = execute(compiler.materialize(new_source, constants), values)
        restored = restore_parent_registers(packet, after)
        assert before[old_output] == after[new_output]
        assert all(before[n] == (restored[n] if n in restored else after[n])
                   for n, _, _, _ in old['source'])
        assert all(before[n] == after[n] for n in packet['unit_factors'])
        for register, group in zip(packet['group_products'], packet['factor_partition']):
            product = 1
            for index in group:
                product *= after[packet['unit_factors'][index]]
            assert product == after[register]
    return dict(complete_output_and_register_identities=cases, signed_cases=cases//2,
                supplied_positive_assignments=cases//2)


def symbolic_audit():
    # Independent coefficient dictionaries in P,S0,S1,S2,S3.
    def add(a, b):
        out = Counter(a)
        out.update(b)
        return dict(out)
    def mul(a, b):
        out = Counter()
        for k, v in a.items():
            for l, w in b.items():
                out[tuple(x+y for x, y in zip(k, l))] += v*w
        return dict(out)
    one = {(0,)*5: 1}
    P, S0, S1, S2, S3 = [{tuple(int(i == j) for i in range(5)): 1} for j in range(5)]
    P2 = mul(P, P)
    assert mul(add(P, one), add(P2, one)) == add(mul(P2, P), add(P2, add(P, one)))
    assert add(S0, mul(P, add(S1, mul(P, add(S2, mul(P, S3)))))) == add(
        add(S0, mul(P, S1)), mul(P2, add(S2, mul(P, S3))))
    minus_one = {(0,)*5: -1}
    assert add(add(P, P), minus_one) == add(P, add(P, minus_one))
    return dict(exact_reusable_repunit_identity=True, exact_selector_prefix_identity=True,
                exact_reusable_radix_identity=True)


def guards_audit():
    old = parent.build_factored()
    mutations = [
        lambda p: p['source'].append(('bad_consumer', '+', 'hist__repunit_factor__52', 1)),
        lambda p: p['source'].append(('bad_consumer', '+', 'hist__pack_product__46', 1)),
        lambda p: p['comparisons'].append(('hist__pack_sum__47', 1)),
        lambda p: p.update(interfaces={'nested': ['hist__pack_product__48', None]}),
        lambda p: p.update(public_registers={'nested': {'factor': 'hist__repunit_factor__52'}}),
        lambda p: p['source'].append(('shared_history_selector_high', '+', 'x', 1)),
        lambda p: p.update(source=[(n, op, a, 2) if n == 'hist__repunit_factor__50'
                                   else (n, op, a, b) for n, op, a, b in p['source']]),
        lambda p: p.update(source=[(n, op, a, 'hist__Shat2') if n == 'hist__pack_product__60'
                                   else (n, op, a, b) for n, op, a, b in p['source']]),
        lambda p: p['source'].append(('bad_consumer', '+', 'twiceB', 1)),
        lambda p: p.update(fusion_interfaces={'nested': ['twiceB']}),
        lambda p: p.update(source=[(n, op, a, 2) if n == 'Bm1'
                                   else (n, op, a, b) for n, op, a, b in p['source']]),
    ]
    for change in mutations:
        p = copy.deepcopy(old)
        change(p)
        try:
            rewrite(p)
        except (AssertionError, KeyError):
            pass
        else:
            raise AssertionError('Incompatible local graph accepted')
    return dict(rejected_incompatible_callers=len(mutations))


def verify():
    records, bases, examples = [], [], []
    for interface in (False, True):
        for n in parent.NORMALIZATIONS:
          for s in parent.SCALE_OPTIONS:
            base = parent.build_base(n, s, interface)
            for use_repunit, use_selectors, use_radix in OPTIONS:
                packet = rewrite(parent.factored.rewrite(base),
                    repunit=use_repunit, selectors=use_selectors, radix=use_radix)
                bases.append(dict(ledger(packet), audit=audit(packet, 265160+len(bases))))
            for plan in parent.search(n, s)['best_by_group_count']:
                compiled, _, _ = parent.partitions.source(base, plan['partition'], plan['anchor'])
                old = parent.factored.rewrite(compiled)
                for use_repunit, use_selectors, use_radix in OPTIONS:
                    records.append(ledger(rewrite(old, repunit=use_repunit, selectors=use_selectors, radix=use_radix)))
        seen = set()
        for witnesses in (None, 43, 44, 45):
            for plan in parent.factored_frontier(witnesses):
                old = parent.build_factored(plan['polynomial']['operations'],
                    merge_bound=interface, witnesses=witnesses)
                key = (tuple(old['normalized_prefixes']), tuple(old.get('positive_scale_prefixes', ())),
                    tuple(tuple(g) for g in old['factor_partition']), old['partition_anchor'])
                if key in seen:
                    continue
                seen.add(key)
                for use_repunit, use_selectors, use_radix in OPTIONS:
                    packet = rewrite(old, repunit=use_repunit, selectors=use_selectors, radix=use_radix)
                    source, output = polynomial_source(packet)
                    encoded = compiler.encode_source(source)
                    rec = dict(ledger(packet),
                        parameters=packet['parameters'], auxiliaries=packet['auxiliaries'],
                        source_sha256=hashlib.sha256(json.dumps(encoded, sort_keys=True).encode()).hexdigest(),
                        audit=audit(packet, 2651000+len(examples), 8))
                    if use_repunit and use_selectors and use_radix:
                        rec['source'] = encoded
                    examples.append(rec)
    assert (len(records), len(bases), len(examples)) == (2464, 224, 308)
    default = ledger(build())
    assert default['polynomial'] == dict(operations=265, multiplications=134,
        additions_subtractions=131, degree_upper_bound=3853, exact_degree_claimed=False)
    assert default['certificate'] == dict(operations=251, multiplications=129,
        additions_subtractions=122, equations=5, witnesses=43)
    frontier = [(c-4, d, w) for c, d, w in parent.summary(parent.factored_frontier())]
    return dict(status='PASS_NEARY_WOODS_UNIVERSAL_SHARED_HISTORY265',
        default=default, frontier=frontier,
        witness_frontiers={str(w): [(c-4,d,v) for c,d,v in parent.summary(parent.factored_frontier(w))]
                           for w in (43,44,45)},
        ledgers=records, base_audits=bases, examples=examples,
        symbolic=symbolic_audit(), guards=guards_audit(),
        complete_output_and_register_identities=16*len(bases)+8*len(examples),
        signed_cases=8*len(bases)+4*len(examples),
        scope='Identical complete polynomials and supplied domains; uniform exact1/2/3/4 gate savings '
              'on the full inherited finite grouping family, with unchanged conservative degrees.')


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--write', action='store_true')
    args = parser.parse_args()
    result = json.loads(json.dumps(verify()))
    target = Path(__file__).with_suffix('.json')
    if args.write:
        target.write_text(json.dumps(result, indent=2, sort_keys=True)+'\n')
    else:
        assert json.loads(target.read_text()) == result, 'receipt mismatch'
    print(result['status'])
    print(result['frontier'])
    print(result['scope'])
