"""Absorb the second recoder repunit as a proved positive unit.

The positive zero set is unchanged. Off-zero polynomials are related by
explicit finalizer corrections, not an unconditional polynomial identity.
"""
import argparse
from collections import Counter
import copy
from functools import lru_cache
import hashlib
import json
from math import gcd
from pathlib import Path
import random

import neary_woods_universal_shared_history265 as parent

compiler = parent.compiler
execute = parent.execute
polynomial_source = parent.polynomial_source
degree_bound = parent.degree_bound
UNIT = 'mask_repunit_unit'
PRODUCT = 'mask_unit_group_product'
REMOVED = ('mask_scale', 'scale')
EXPECTED = [(263, 3857, 43), (264, 3441, 43), (265, 3395, 43),
            (266, 2277, 44), (267, 1509, 44), (268, 1463, 44),
            (269, 1100, 44), (270, 1054, 44), (271, 734, 44),
            (272, 706, 44), (273, 608, 44)]


@lru_cache(None)
def canonical_parent(normalized, scaled, interface, partition, anchor, direct=False):
    base = parent.parent.build_base(normalized, scaled, interface)
    if direct:
        assert partition == tuple(map(tuple, base['factor_partition'])) and anchor == base['partition_anchor']
        old = base
    else:
        old, _, _ = parent.parent.partitions.source(base, partition, anchor)
    return parent.rewrite(parent.parent.factored.rewrite(old))


def guard_parent(old):
    """The sign proof uses the entire frozen outer/native source contract."""
    assert not old.get('mask_repunit_as_unit')
    partition = tuple(tuple(group) for group in old['factor_partition'])
    checked = canonical_parent(tuple(old['normalized_prefixes']),
        tuple(old.get('positive_scale_prefixes', ())), old['bound_is_program_E'],
        partition, old['partition_anchor'])
    if old['source'] != checked['source']:
        # The frozen one-group base keeps historical product labels across
        # checksum specialization; explicit regrouping uses compact labels.
        checked = canonical_parent(tuple(old['normalized_prefixes']),
            tuple(old.get('positive_scale_prefixes', ())), old['bound_is_program_E'],
            partition, old['partition_anchor'], True)
    for key in ('source', 'comparisons', 'parameters', 'auxiliaries', 'unit_factors',
                'unit_register', 'unit_product', 'factor_partition', 'partition_anchor',
                'group_products', 'fixed_numerals', 'width', 'interfaces',
                'public_registers', 'fusion_interfaces', 'projected_coordinates',
                'normalized_prefixes', 'positive_scale_prefixes', 'bound_is_program_E'):
        # The parent partition API preserves the caller's tuple/list shape.
        a, b = old.get(key), checked.get(key)
        if key == 'factor_partition':
            a, b = tuple(map(tuple, a)), tuple(map(tuple, b))
        assert a == b, key
    compiler.check_source(old)
    rows = {n: (op, a, b) for n, op, a, b in old['source']}
    assert rows['mask_scale'] == ('+', 'mask_product', 1)
    assert rows['mask_product'] == ('*', 'twiceBm1', 'K')
    assert rows['twiceBm1'] == ('+', 'B', 'Bm1')
    assert rows['Bm1'] == ('-', 'B', 1)
    assert rows['scale'] == ('*', 'input_bound', 'repunit_P')
    assert rows['K'] == ('+', 'quotient_hat', 'fusion_output_slack')
    assert old['comparisons'].count(REMOVED) == 1
    assert all('mask_scale' not in (a, b) for _, _, a, b in old['source'])
    for key in ('unit_factors', 'group_products', 'interfaces', 'public_registers',
                'fusion_interfaces', 'projected_coordinates'):
        assert 'mask_scale' not in parent.leaves(old.get(key, {})), key
    assert not {UNIT, PRODUCT} & (set(rows) | set(old['parameters']+old['auxiliaries']))


def _rewrite(old, group):
    assert type(group) is int and 0 <= group < len(old['group_products'])
    prior_product = old['group_products'][group]
    source = [r for r in old['source'] if r[0] != 'mask_scale']
    source += [(UNIT, '-', 'scale', 'mask_product'),
               (PRODUCT, '*', prior_product, UNIT)]
    pairs = [(PRODUCT if a == prior_product else a, b)
             for a, b in old['comparisons'] if (a, b) != REMOVED]
    products = list(old['group_products'])
    products[group] = PRODUCT
    partition = [list(g) for g in old['factor_partition']]
    partition[group].append(len(old['unit_factors']))
    count = Counter('M' if op == '*' else 'A' for _, op, _, _ in source)
    packet = dict(old, source=source, comparisons=pairs,
        unit_factors=old['unit_factors']+[UNIT], group_products=products,
        unit_register=PRODUCT if old['unit_register'] == prior_product else old['unit_register'],
        factor_partition=partition, operations=len(source), equations=len(pairs),
        multiplications=count['M'], additions_subtractions=count['A'],
        mask_repunit_as_unit=True, mask_unit_parent=old, mask_unit_group=group,
        mask_unit_removed_comparison=REMOVED, mask_unit_removed_register='mask_scale',
        identical_complete_polynomial=False, identical_positive_coordinates=True,
        identical_positive_zero_set=True)
    assert packet['operations'] == old['operations']+1
    assert count['M'] == old['multiplications']+1
    assert count['A'] == old['additions_subtractions']
    assert packet['equations'] == old['equations']-1
    compiler.check_source(packet)
    return packet


def rewrite(old, *, group=None):
    """Insert the new unit into one existing group, defaulting to least degree.

    This minimizes only its placement in the supplied fixed partition.
    It does not rerun the parent's partition/strong-treatment search.
    """
    guard_parent(old)
    if group is not None:
        return _rewrite(old, group)
    choices = [_rewrite(old, j) for j in range(len(old['group_products']))]
    return min(choices, key=lambda p: (degree_bound(p)['degree_upper_bound'], p['mask_unit_group']))


def build(operations=263, *, merge_bound=True, witnesses=None):
    return rewrite(parent.build(operations+2, merge_bound=merge_bound, witnesses=witnesses))


def ledger(packet):
    old = packet['mask_unit_parent']
    source, output = polynomial_source(packet)
    old_source, _ = polynomial_source(old)
    count = Counter('M' if op == '*' else 'A' for _, op, _, _ in source)
    assert len(source) == len(old_source)-2
    assert packet['parameters'] == old['parameters'] and packet['auxiliaries'] == old['auxiliaries']
    parent.parent.loader.source_closure(source, output)
    bound = degree_bound(packet)
    return dict(normalized_prefixes=packet['normalized_prefixes'],
        positive_scale_prefixes=packet.get('positive_scale_prefixes', ()),
        bound_is_program_E=packet['bound_is_program_E'], group=packet['mask_unit_group'],
        factor_partition=packet['factor_partition'], partition_anchor=packet['partition_anchor'],
        certificate={k: packet[k] for k in ('operations', 'multiplications',
            'additions_subtractions', 'equations', 'witnesses')},
        polynomial=dict(operations=len(source), multiplications=count['M'],
            additions_subtractions=count['A'], degree_upper_bound=bound['degree_upper_bound'],
            exact_degree_claimed=False), unit_degree_bound=bound['factor_degree_bounds'][UNIT],
        output=output)


def audit(packet, seed, cases=16):
    old = packet['mask_unit_parent']
    old_source, old_output = polynomial_source(old)
    source, output = polynomial_source(packet)
    rng = random.Random(seed)
    selected, anchor = packet['mask_unit_group'], old['partition_anchor']
    for case in range(cases):
        draw = lambda: rng.randrange(1, 5) if case < cases//2 else rng.randrange(-3, 4)
        fixed = {n: draw() for n in compiler.NUMERALS}
        values = {n: draw() for n in packet['parameters']+packet['auxiliaries']}
        before = execute(compiler.materialize(old_source, fixed), values)
        after = execute(compiler.materialize(source, fixed), values)
        assert all(before[n] == after[n] for n, _, _, _ in old['source'] if n != 'mask_scale')
        unit = before['scale']-before['mask_product']
        assert after[UNIT] == unit and before['mask_scale']-before['scale'] == 1-unit
        groups = [before[n] for n in old['group_products']]
        for j, (register, indices) in enumerate(zip(packet['group_products'], packet['factor_partition'])):
            product = 1
            for index in indices:
                product *= after[packet['unit_factors'][index]]
            assert product == after[register] == groups[j]*(unit if j == selected else 1)
        if selected == anchor:
            expected = unit*(before[old_output]+1)-unit*groups[selected]*(1-unit)**2-1
        else:
            weight = 1 if anchor is None else groups[anchor]
            correction = (unit*groups[selected]-1)**2-(groups[selected]-1)**2-(1-unit)**2
            expected = before[old_output]+weight*correction
        assert after[output] == expected
    return dict(complete_corrected_output_and_register_cases=cases, signed_cases=cases//2)


def margin_audit():
    """Actual emitted outer rows under both repunit signs, without native zeros."""
    packet = build()
    rng = random.Random(263120)
    count = negative = nondyadic = 0
    for D in (3, 4, 5):
      for sign in (-1, 1):
       for q in range(8, 17):
        ell, x, z, gap = 3, 1, 2, 1
        Q = ((1 << D)-1)*(q+z+gap)+1
        B = (1 << (D-1))*Q
        modulus = 2*B-1
        if gcd(q, modulus) != 1:
            continue
        coefficient = q*(B-1)**2
        target = sign-q*((B-1)*ell+1)
        duration_quotient = (target*pow(coefficient, -1, modulus)) % modulus or modulus
        J = (B-1)*duration_quotient+ell
        P = (B-1)*J+1
        S = q*P
        assert (S-sign) % modulus == 0
        K = (S-sign)//modulus
        h = 1+rng.randrange(4)
        assert K > h
        fixed = {n: 2 for n in compiler.NUMERALS}
        fixed.update(repunit_divisor=(1 << D)-1, recoder_radix=1 << (D-1),
                     history_radix=2, terminal_scale=2, terminal_offset=1)
        values = {n: 1 for n in packet['parameters']+packet['auxiliaries']}
        values.update(x=x, z=z, program_E=1, program_duration_gap=2,
            input_slack=q-x-ell, power_gap=gap, duration_quotient=duration_quotient,
            quotient_hat=h, fusion_output_slack=K-h)
        values.update({f'hist__Shat{i}':2+rng.randrange(3) for i in range(4)})
        rows = compiler.materialize(packet['source'], fixed)
        e = execute(rows, values)
        values['hist__global_bound'] = e['hist__P__10']-5
        assert min(values.values()) > 0
        e = execute(rows, values)
        assert e[UNIT] == sign
        assert e['hist__global_lhs__15'] == e['hist__P__10']
        assert e['input_bound'] == q and e['B'] == B and e['scale'] == S
        low = e['fusion_low_q']
        A = e['factored_pack_A_plus_one']-1
        Bp, Zp, qjoint = e['and__padded_B'], e['and__F3'], e['and__q']
        F1, F2 = A-Zp, Bp-Zp
        F0 = qjoint-1-F1-F2-Zp
        assert min(F0, F1, F2, Zp) > 0 and F0+F1+F2+Zp == qjoint-1
        assert [F0 % 16, F1 % 16, F2 % 16, Zp % 16] == [1, 4, 2, 8]
        assert F0+qjoint*F1+qjoint**2*F2+qjoint**3*Zp == e['and__bs_packed']
        assert 0 < e['factored_pack_low_A_plus_one']-1 < low
        assert 0 < e['fusion_low_padded_B'] < low
        assert 0 < e['fusion_low_F3'] < low
        count += 1
        negative += sign == -1
        nondyadic += bool(q & (q-1))
    return dict(actual_source_outer_margin_cases=count, negative_mask_sign_cases=negative,
        nondyadic_input_scale_cases=nondyadic,
        scope='Positive supplied tuples satisfying the signed mask and history global equations only; not native Pell zeros.')


def sign_audit():
    rng = random.Random(263111)
    cases = carry = 0
    for b in range(2, 49):
        modulus = (1 << (b+1))-1
        for e in range(4*(b+1)+1):
            residue = pow(2, e, modulus)
            assert residue == 1 << (e % (b+1))
            assert residue != modulus-1
            cases += 1
    for t in range(4, 21):
      for _ in range(16):
        remaining = (1 << (t-4))-1
        high = []
        for _ in range(3):
            value = rng.randrange(remaining+1)
            high.append(value)
            remaining -= value
        high.append(remaining)
        fields = [16*a+d for a, d in zip(high, (1, 4, 2, 8))]
        q = 1 << t
        r = sum(v*q**i for i, v in enumerate(fields))
        assert all(0 < v < q for v in fields) and sum(fields) == q-1
        v2 = ((r-1) & -(r-1)).bit_length()-1
        assert r % 16 == 1 and v2 >= 4
        assert (r-2).bit_count() == r.bit_count()+v2-2 >= t+2
        carry += 1
    return dict(Mersenne_residue_cases=cases, negative_joint_index_population_cases=carry)


def guards_audit():
    old = parent.build()
    changes = [
        lambda p: p['source'].append(('unexpected_mask_consumer', '+', 'mask_scale', 1)),
        lambda p: p.update(public_registers={'extra': ['mask_scale']}),
        lambda p: p['comparisons'].append(('scale', 1)),
        lambda p: p['comparisons'].remove(REMOVED),
        lambda p: p.update(source=[(n, op, a, 2) if n == 'mask_scale' else (n, op, a, b)
                                   for n, op, a, b in p['source']]),
        lambda p: p.update(source=[(n, op, a, 14) if n == 'factored_pack_low_A_plus_one' else (n, op, a, b)
                                   for n, op, a, b in p['source']]),
        lambda p: p.update(auxiliaries=p['auxiliaries']+['unexpected_positive_coordinate']),
        lambda p: p.update(unit_factors=p['unit_factors'][:-1]),
    ]
    for change in changes:
        bad = copy.deepcopy(old)
        change(bad)
        try:
            rewrite(bad)
        except (AssertionError, KeyError, ValueError):
            pass
        else:
            raise AssertionError('incompatible source accepted')
    return dict(rejected_incompatible_callers=len(changes))


def verify():
    bases, placements, examples, frontiers = [], [], [], {}
    for interface in (False, True):
        for n in parent.parent.NORMALIZATIONS:
          for s in parent.parent.SCALE_OPTIONS:
            base = parent.parent.build_base(n, s, interface)
            old = parent.rewrite(parent.parent.factored.rewrite(base))
            packet = rewrite(old)
            bases.append(dict(ledger(packet), audit=audit(packet, 263160+len(bases))))
        seen = set()
        for witnesses in (None, 43, 44, 45):
            frontier = []
            for plan in parent.parent.factored_frontier(witnesses):
                old_cost = plan['polynomial']['operations']-4
                old = parent.build(old_cost, merge_bound=interface, witnesses=witnesses)
                packet = rewrite(old)
                rec = ledger(packet)
                frontier.append((rec['polynomial']['operations'],
                    rec['polynomial']['degree_upper_bound'], packet['witnesses']))
                key = (tuple(packet['normalized_prefixes']), tuple(packet.get('positive_scale_prefixes', ())),
                    tuple(map(tuple, old['factor_partition'])), old['partition_anchor'])
                if key in seen:
                    continue
                seen.add(key)
                for group in range(len(old['group_products'])):
                    option = rewrite(old, group=group)
                    placements.append(dict(ledger(option), audit=audit(option, 2631000+len(placements), 8)))
                source, output = polynomial_source(packet)
                encoded = compiler.encode_source(source)
                examples.append(dict(rec, source=encoded, parameters=packet['parameters'],
                    auxiliaries=packet['auxiliaries'],
                    source_sha256=hashlib.sha256(json.dumps(encoded, sort_keys=True).encode()).hexdigest()))
            if interface:
                frontiers[str(witnesses)] = frontier
    assert frontiers['None'] == EXPECTED
    default = ledger(build())
    assert default['certificate'] == dict(operations=252, multiplications=130,
        additions_subtractions=122, equations=4, witnesses=43)
    assert default['polynomial'] == dict(operations=263, multiplications=134,
        additions_subtractions=129, degree_upper_bound=3857, exact_degree_claimed=False)
    return dict(status='PASS_NEARY_WOODS_UNIVERSAL_MASK_UNIT263', default=default,
        mapped_frontiers=frontiers, bases=bases, placements=placements, selected_sources=examples,
        ledger_count=len(bases)+len(placements),
        corrected_output_cases=16*len(bases)+8*len(placements),
        signed_cases=8*len(bases)+4*len(placements),
        outer_margins=margin_audit(), sign_checks=sign_audit(), guards=guards_audit(),
        scope='Identical complete positive zero sets for every guarded fixed265 parent. '
              'The fixed U9 numerals, valid program slices, ordinary input and exact counter are unchanged. '
              'Mapped selected schedules with best single-factor placement only; no new global partition optimum. '
              'Off-zero source outputs obey explicit finalizer corrections, not equality. Degree bounds are upper bounds;75/87 unchanged.')


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
    print(result['default'])
    print(result['mapped_frontiers']['None'])
