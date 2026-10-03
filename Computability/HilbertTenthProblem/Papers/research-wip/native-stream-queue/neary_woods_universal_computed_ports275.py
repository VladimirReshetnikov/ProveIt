"""Compute all three AND truth fields using retained joined-port margins.

The field may be signed off zero. Two retained outer comparisons make it
positive before native typing. Two-port projection is a positive-zero graph
bijection; the checksum projection preserves the complete outer relation.
"""
import argparse
from collections import Counter
from functools import lru_cache
import hashlib
import json
from math import gcd
from pathlib import Path
import random

import neary_woods_universal_duration_floor282 as parent

compiler = parent.compiler
units = parent.units
execute = parent.execute
MODES = ('A', 'AB', 'all')
FIELD = 'and__F1'
OLD_PORT = 'and__input_A'
PORT = 'and__padded_A'
OUTPUT_FIELD = 'and__F3'


def remap_tree(value, aliases):
    if isinstance(value, str):
        while value in aliases:
            value = aliases[value]
            if not isinstance(value, str):
                break
        return value
    if isinstance(value, dict):
        return {k: remap_tree(v, aliases) for k, v in value.items()}
    if isinstance(value, list):
        return [remap_tree(v, aliases) for v in value]
    if isinstance(value, tuple):
        return tuple(remap_tree(v, aliases) for v in value)
    return value


@lru_cache(None)
def selected_parent(cost, merge_bound, witnesses):
    return parent.build(cost, merge_bound=merge_bound, witnesses=witnesses)


def rewrite(old, mode='all'):
    assert mode in MODES
    assert old.get('duration_input_floor') and not old.get('computed_joined_input_field')
    compiler.check_source(old)
    cost = old['operations']+3*old['equations']-1
    checked = selected_parent(cost, old['bound_is_program_E'], old['witnesses'])
    # This theorem is for the literal selected parent family. In particular,
    # every outer row/comparison used in the pretyping margin is guarded.
    for key in ('source', 'comparisons', 'parameters', 'auxiliaries', 'unit_factors',
                'unit_register', 'unit_product', 'factor_partition', 'partition_anchor',
                'group_products', 'width', 'positive_scale_prefixes'):
        assert old[key] == checked[key], key
    for key in ('interfaces', 'public_registers'):
        assert old.get(key, {}) == checked.get(key, {}), key
    rows = {n: (op, a, b) for n, op, a, b in old['source']}
    assert rows[OLD_PORT] == ('+', FIELD, OUTPUT_FIELD)
    assert rows[PORT] == ('+', 'fusion_low_padded_A', 'fusion_high_A')
    assert rows[OUTPUT_FIELD] == ('+', 'fusion_low_F3', 'fusion_high_Z')
    assert rows['hist__joined_H__89'] == ('+', 'hist__joined_H__88', 'hist__top_history__87')
    assert rows['hist__joined_H__88'] == ('+', 'hist__common_joined__83', 'hist__history_batch__68')
    assert rows['hist__joined_Z__96'] == ('+', 'hist__common_joined__83', 'hist__unhat_pack__74')
    removed = [(OLD_PORT, PORT)]
    assert old['comparisons'].count(removed[0]) == 1
    assert ('mask_scale', 'scale') in old['comparisons']
    assert ('hist__global_lhs__15', 'hist__P__10') in old['comparisons']
    consumers = lambda v: {n for n, _, a, b in old['source'] if v in (a, b)}
    assert consumers(FIELD) == {OLD_PORT, 'and__bs_p3'}
    assert consumers(OLD_PORT) == {'and__bs_Q'}
    assert all(FIELD not in pair for pair in old['comparisons'])
    assert all(pair == removed[0] for pair in old['comparisons'] if OLD_PORT in pair)
    assert old['auxiliaries'].count(FIELD) == 1 and FIELD not in old['parameters']
    aliases = {OLD_PORT: PORT}
    drop = {OLD_PORT}
    fields = [FIELD]
    additions = [(FIELD, '-', PORT, OUTPUT_FIELD)]
    if mode in ('AB', 'all'):
        assert rows['and__input_B'] == ('+', 'and__F2', OUTPUT_FIELD)
        assert not consumers('and__input_B')
        pair = ('and__input_B', 'and__padded_B')
        assert old['comparisons'].count(pair) == 1
        assert all(p == pair for p in old['comparisons'] if 'and__input_B' in p)
        removed.append(pair)
        aliases['and__input_B'] = 'and__padded_B'
        drop.add('and__input_B')
        fields.append('and__F2')
        additions.append(('and__F2', '-', 'and__padded_B', OUTPUT_FIELD))
    checksum = 'and__bs_q'
    if mode == 'all':
        assert rows['and__shared_sum02'] == ('+', 'and__F0', 'and__F2')
        assert rows['and__bs_Q'] == ('+', 'and__shared_sum02', OLD_PORT)
        assert rows[checksum] == ('-', 'and__q', 'and__bs_Q')
        assert consumers('and__shared_sum02') == {'and__bs_Q'}
        assert consumers('and__bs_Q') == {checksum}
        assert consumers('and__F0') == {'and__shared_sum02', 'and__bs_packed'}
        drop |= {'and__shared_sum02', 'and__bs_Q', checksum}
        aliases[checksum] = 1
        fields.append('and__F0')
        additions += [('computed_ports_remaining', '-', 'and__q', PORT),
                      ('computed_ports_before_one', '-', 'computed_ports_remaining', 'and__F2'),
                      ('and__F0', '-', 'computed_ports_before_one', 1)]
    source = []
    simplified = []
    for n, op, a, b in old['source']:
        if n in drop:
            continue
        a, b = remap_tree(a, aliases), remap_tree(b, aliases)
        if op == '*' and (a == 1 or b == 1):
            assert n.startswith('partition_product_')
            aliases[n] = b if a == 1 else a
            simplified.append(n)
        else:
            source.append((n, op, a, b))
    source += additions
    auxiliaries = [n for n in old['auxiliaries'] if n not in fields]
    source = parent.parent.parent.sort_source(source, old['parameters']+auxiliaries)
    pairs = [remap_tree(pair, aliases) for pair in old['comparisons'] if pair not in removed]
    trivial = [pair for pair in pairs if pair == (1, 1)]
    pairs = [pair for pair in pairs if pair != (1, 1)]
    anchor = remap_tree(old['unit_register'], aliases)
    anchored = old['unit_product'] and anchor != 1
    if not anchored:
        anchor = None
    factors = list(old['unit_factors'])
    groups, new_anchor = list(old['factor_partition']), old['partition_anchor']
    if mode == 'all':
        index = factors.index(checksum)
        factors.pop(index)
        rebuilt = []
        for i, group in enumerate(groups):
            group = [j-(j > index) for j in group if j != index]
            if i == old['partition_anchor']:
                new_anchor = len(rebuilt) if group else None
            if group:
                rebuilt.append(group)
        groups = rebuilt
    count = Counter('M' if op == '*' else 'A' for _, op, _, _ in source)
    group_products = [remap_tree(v, aliases) for v in old['group_products']]
    group_products = [v for v in group_products if v != 1]
    assert len(group_products) == len(groups)
    assert all(v in {n for n, _, _, _ in source} for v in group_products)
    packet = dict(old, source=source, comparisons=pairs, auxiliaries=auxiliaries,
        operations=len(source), multiplications=count['M'], additions_subtractions=count['A'],
        equations=len(pairs), witnesses=len(auxiliaries), computed_joined_input_field=True,
        computed_ports_parent=old, computed_ports_mode=mode, computed_fields=fields,
        removed_port_comparisons=removed, computed_port_aliases=aliases,
        simplified_products=simplified, removed_trivial_comparisons=trivial,
        positive_computed_fields_at_zeros=True, unit_factors=factors,
        unit_register=anchor, unit_product=anchored, factor_partition=groups,
        partition_anchor=new_anchor, group_products=group_products,
        accepted_outer_relation_only=mode == 'all',
        historical_parents_unchanged=True)
    for key in ('interfaces', 'public_registers'):
        if key in old:
            packet[key] = remap_tree(old[key], aliases)
    assert len(source) == old['operations']-len(simplified)
    assert packet['equations'] == old['equations']-len(removed)-len(trivial)
    assert packet['witnesses'] == old['witnesses']-len(fields)
    compiler.check_source(packet)
    return packet


def build(parent_operations=282, *, merge_bound=True, parent_witnesses=None, mode='all'):
    return rewrite(parent.build(parent_operations, merge_bound=merge_bound,
        witnesses=parent_witnesses), mode)


polynomial_source = parent.polynomial_source
degree_bound = parent.degree_bound


def ledger(packet):
    source, output = polynomial_source(packet)
    count = Counter('M' if op == '*' else 'A' for _, op, _, _ in source)
    bound = degree_bound(packet)
    return dict(certificate={n: packet[n] for n in ('operations', 'multiplications',
        'additions_subtractions', 'equations', 'witnesses')},
        polynomial=dict(operations=len(source), multiplications=count['M'],
            additions_subtractions=count['A'], degree_upper_bound=bound['degree_upper_bound'],
            exact_degree_claimed=False), parameters=packet['parameters'],
        bound_is_program_E=packet['bound_is_program_E'], output=output,
        factor_partition=packet['factor_partition'], partition_anchor=packet['partition_anchor'])


def lift_to_parent(packet, values):
    env = execute(packet['source'], values)
    return dict(values, **{field: env[field] for field in packet['computed_fields']})


def project_from_parent(packet, values, *, normalize_negative_checksum=False):
    if normalize_negative_checksum and packet['computed_ports_mode'] == 'all':
        env = execute(packet['computed_ports_parent']['source'], values)
        assert env['and__bs_q'] in (-1, 1)
        if env['and__bs_q'] == -1:
            assert env['geo__index_unit'] == 1 and env['and__index_unit'] == -1
            assert env['geo__linear_unit'] == env['and__linear_unit'] == 1
            values = dict(values, **{'and__bound_beta': values['and__bound_beta']+2})
    return {n: v for n, v in values.items() if n not in packet['computed_fields']}


def audit(packet, seed):
    rng = random.Random(seed)
    old = packet['computed_ports_parent']
    old_source, old_output = polynomial_source(old)
    negative = positive_negative = 0
    for case in range(32):
        positive = case < 16
        draw = lambda: rng.randrange(1, 8) if positive else rng.randrange(-5, 6)
        numerals = {n: draw() for n in compiler.NUMERALS}
        if positive:
            numerals.update(recoder_radix=4, repunit_divisor=7, history_radix=8)
        literal = units.constants_parent.materialize_packet(packet, numerals)
        values = {n: draw() for n in packet['parameters']+packet['auxiliaries']}
        # Force some positive off-zero tuples outside the retained global bound.
        if positive and case % 4 == 0:
            initial = execute(literal['source'], values)
            values['hist__ZUhat0'] += abs(initial[FIELD])+1
        source, output = polynomial_source(literal)
        env = execute(source, values)
        restored = lift_to_parent(literal, values)
        before = execute(compiler.materialize(old_source, numerals), restored)
        assert before[OLD_PORT] == env[PORT]
        assert before[old_output] == env[output]
        for n, _, _, _ in old['source']:
            if n in env:
                assert before[n] == env[n]
            elif n in packet['computed_port_aliases']:
                alias = remap_tree(n, packet['computed_port_aliases'])
                assert before[n] == (alias if isinstance(alias, int) else env[alias])
            else:
                assert n in ('and__shared_sum02', 'and__bs_Q')
        assert all(before[n] == env[n] for n in packet['unit_factors'])
        for register, group in zip(packet['group_products'], packet['factor_partition']):
            expected_product = 1
            for index in group:
                expected_product *= env[packet['unit_factors'][index]]
            assert env[register] == expected_product
        assert project_from_parent(literal, restored) == values
        negative += env[FIELD] < 0
        positive_negative += positive and env[FIELD] < 0
    assert positive_negative >= 4
    return dict(whole_output_identities=32, signed_assignments=16,
        coordinate_round_trips=32, negative_computed_fields=negative,
        positive_off_zero_tuples_with_negative_field=positive_negative)


def outer_margin_audit():
    packet = build()
    rng = random.Random(279154)
    cases = nondyadic = 0
    for D in (3, 4, 5):
      for attempt in range(128):
        numerals = {n: 2 for n in compiler.NUMERALS}
        numerals.update(recoder_radix=1 << (D-1), repunit_divisor=(1 << D)-1,
                        history_radix=8, terminal_scale=4, terminal_offset=2)
        literal = units.constants_parent.materialize_packet(packet, numerals)
        v = {n: rng.randrange(1, 5) for n in packet['parameters']+packet['auxiliaries']}
        # Set the mask comparison exactly using a congruence in the positive
        # duration quotient, without requiring any dyadic base or native norm.
        ell = v['program_E']+v['program_duration_gap']
        q = v['x']+ell+v['input_slack']
        Q = ((1 << D)-1)*(q+v['z']+v['power_gap'])+1
        B = (1 << (D-1))*Q
        M = 2*B-1
        if gcd(q, M) != 1:
            continue
        coefficient = q*(B-1)**2
        quotient = ((1-q*((B-1)*ell+1))*pow(coefficient, -1, M)) % M
        v['duration_quotient'] = quotient+M
        J = (B-1)*v['duration_quotient']+ell
        S = q*((B-1)*J+1)
        K, remainder = divmod(S-1, M)
        assert remainder == 0 and K > v['quotient_hat']
        v['fusion_output_slack'] = K-v['quotient_hat']
        v['hist__Shat0'] += 1
        env = execute(literal['source'], v)
        P = env['hist__P__10']
        total = sum(v[n] for n in ('hist__H_U', 'hist__H_V',
            'hist__ZUhat0', 'hist__ZVhat0', 'hist__ZVhat1'))
        v['hist__global_bound'] = P-total
        assert v['hist__global_bound'] > 0
        env = execute(literal['source'], v)
        H, V = v['hist__H_U'], v['hist__H_V']
        Hb = H+P*V+P*P*V
        Zb = v['hist__ZUhat0']-1+P*(v['hist__ZVhat0']-1)+P*P*(v['hist__ZVhat1']-1)
        Bh = env['hist__B__3']
        high_difference = Bh*P**9+Hb-Zb
        assert env['mask_scale'] == env['scale'] == S
        assert env['hist__global_lhs__15'] == P >= 6
        assert 0 <= Zb < P**3 and high_difference >= 1
        assert env['hist__joined_H__89']-env['hist__joined_Z__96'] == high_difference
        assert 1 <= env['projected_Ahat'] < S
        assert 0 < env['fusion_low_F3'] < env['fusion_low_q']
        assert env[FIELD] == (env['fusion_low_padded_A']-env['fusion_low_F3']
                             +env['fusion_low_q']*high_difference) > 0
        Mh, Zh = env['hist__joined_M__95'], env['hist__joined_Z__96']
        assert Mh-Zh > 1
        assert Mh <= P**10-1
        assert P**11-high_difference-Mh >= 2
        assert 0 < env['fusion_low_padded_A'] < env['fusion_low_q']
        assert 0 < env['fusion_low_padded_B'] < env['fusion_low_q']
        assert env['and__F2'] > 0 and env['and__F0'] > 0
        assert sum(env[f'and__F{i}'] for i in range(4))+1 == env['and__q']
        assert min(v.values()) > 0
        cases += 1
        nondyadic += q & (q-1) != 0
    assert cases >= 128 and nondyadic > 0
    return dict(positive_outer_margin_cases=cases, nondyadic_input_bases=nondyadic,
        scope='Only mask and global-bound comparisons imposed; no native Pell zeros or typed histories claimed.')


def guard_audit():
    import copy
    original = parent.build()
    changes = []
    def change_row(name, replacement):
        def mutate(p):
            p['source'] = [replacement if row[0] == name else row for row in p['source']]
        return mutate
    changes += [change_row('hist__joined_Z__96', ('hist__joined_Z__96', '+',
                'hist__common_joined__83', 'hist__history_batch__68')),
                change_row('K', ('K', '-', 'quotient_hat', 'fusion_output_slack')),
                lambda p: p['comparisons'].remove(('mask_scale', 'scale')),
                lambda p: p['comparisons'].remove(('hist__global_lhs__15', 'hist__P__10')),
                lambda p: p.update(interfaces={'nested': [FIELD, None]}),
                lambda p: p.update(public_registers={'nested': {'private': OLD_PORT}}),
                lambda p: p['parameters'].append(FIELD)]
    rejected = 0
    for mutate in changes:
        p = copy.deepcopy(original)
        mutate(p)
        try:
            rewrite(p)
        except (AssertionError, KeyError, StopIteration):
            rejected += 1
        else:
            raise AssertionError('Unsupported caller modification accepted')
    return dict(rejected_incompatible_parents=rejected)


def family_frontier(records):
    result, least = [], float('inf')
    ordered = sorted(records, key=lambda r: (r['polynomial']['operations'],
        r['polynomial']['degree_upper_bound'], r['certificate']['witnesses']))
    for r in ordered:
        degree = r['polynomial']['degree_upper_bound']
        if degree < least:
            result.append((r['polynomial']['operations'], degree, r['certificate']['witnesses']))
            least = degree
    return result


def verify():
    records = []
    for interface in (False, True):
      for mode in MODES:
       choices = [(o, None) for o, _, _ in parent.EXPECTED]+[(289, 46)]
       for operations, witnesses in choices:
        packet = build(operations, merge_bound=interface, parent_witnesses=witnesses, mode=mode)
        rec = ledger(packet)
        old = packet['computed_ports_parent']
        saved = 3 if mode == 'A' else 6 if mode == 'AB' else (
            9 if packet['removed_trivial_comparisons'] else 7)
        assert rec['polynomial']['operations'] == operations-saved
        assert packet['witnesses'] == old['witnesses']-len(packet['computed_fields'])
        if mode == 'A':
            assert degree_bound(packet) == degree_bound(old)
        assert degree_bound(packet)['degree_upper_bound'] <= degree_bound(old)['degree_upper_bound']
        rec.update(parent_polynomial_operations=operations, mode=mode,
                   restricted_parent_witnesses=witnesses,
                   simplified_products=packet['simplified_products'],
                   removed_trivial_comparisons=packet['removed_trivial_comparisons'])
        rec['audit'] = audit(packet, 275282+len(records))
        source, output = polynomial_source(packet)
        parent.parent.parent.source_closure(source, output)
        encoded = compiler.encode_source(source)
        rec.update(source=encoded, auxiliaries=packet['auxiliaries'],
            source_sha256=hashlib.sha256(json.dumps(encoded, sort_keys=True).encode()).hexdigest())
        records.append(rec)
    actual = [r for r in records if r['bound_is_program_E'] and r['mode'] == 'all']
    default = ledger(build())
    assert default['polynomial'] == dict(operations=275, multiplications=136,
        additions_subtractions=139, degree_upper_bound=3853, exact_degree_claimed=False)
    assert default['certificate']['operations'] == 261
    assert default['certificate']['equations'] == 5
    assert default['certificate']['witnesses'] == 43
    return dict(status='PASS_NEARY_WOODS_UNIVERSAL_COMPUTED_PORTS275',
        default=default, mapped_cost_degree_frontier=family_frontier(actual),
        fixed43_mapped_frontier=family_frontier([r for r in actual if r['certificate']['witnesses'] == 43]),
        ledgers=records, outer_margin=outer_margin_audit(), guards=guard_audit(),
        scope='Complete accepted-outer equivalence with selected282 parents; F1/F2-only forms are positive-zero graph bijections. No global partition optimum claimed.')


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--write', action='store_true')
    args = parser.parse_args()
    result = verify()
    target = Path(__file__).with_suffix('.json')
    if args.write:
        target.write_text(json.dumps(result, indent=2, sort_keys=True)+'\n')
    else:
        assert json.loads(target.read_text()) == json.loads(json.dumps(result))
    print(result['status'])
    print(result['mapped_cost_degree_frontier'])
    print(result['scope'])
