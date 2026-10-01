"""Fixed-arity complete histories for positive residue-affine maps.

The shortcut-Collatz example is not asserted universal. Generic iteration
is fully paid; the prime-coded universal substrate's loader is separate.
"""
import argparse
from collections import Counter
from itertools import product
import hashlib
import json
from pathlib import Path
import random

import wang_b_packed_tape as native_host
import native_binary_positive_scale as positive_scale
import native_binary_computed_fields as fields
import native_binary_norm_units as units
import native_binary_index_coupled_units as coupled

COLLATZ = ((3, 2), (1, 1))
FORMS = ('raw', 'scaled', 'projected', 'units', 'coupled')


def normalize(table):
    table = tuple(tuple(row) for row in table)
    assert table and all(len(row) == 2 for row in table)
    assert all(isinstance(a, int) and a >= 0 and isinstance(d, int) and d >= 1
               for a, d in table)
    return table


def step(table, value):
    assert value > 0
    quotient, residue = divmod(value-1, len(table))
    slope, offset = table[residue]
    return slope*quotient+offset


def _build(table, form, baseline, shared_selector_sum):
    m = len(table)
    classes = sorted(set(a for a, _ in table)-{baseline})
    g = len(classes)
    gates = native_host.Gates()
    emit = gates.emit
    summ = lambda terms, label: gates.sum(terms, label) if terms else 0
    edges = [emit('-', f'edge{i}_hat', 1, 'edge') for i in range(m)]
    J = summ(edges, 'selector_sum')
    W = emit('-', 'quotient_hat', 1, 'quotient_word')
    products = [emit('-', f'product{i}_hat', 1, 'class_product') for i in range(g)]
    h = summ(['input', 'target', 'height_slack'], 'height')
    K = 1
    while K < max(4, m+1, max(a+d for a, d in table)+1):
        K *= 2
    B = emit('*', K, h, 'radix')
    Bm = emit('-', B, 1, 'radix_minus_one')
    P = emit('+', emit('*', Bm, J, 'scale_minus_one'), 1, 'scale')
    selectors = [summ([edges[i] for i, (a, _) in enumerate(table) if a == slope],
                      'class_selector') for slope in classes]
    range_mask = emit('*', emit('-', h, 1, 'height_minus_one'), J, 'range_mask')
    if shared_selector_sum:
        offset_base = min(d for _, d in table)
        offsets = [emit('*', offset_base, J, 'offset_baseline')]
        offsets += [emit('*', d-offset_base, edge, 'offset_difference')
                    for (_, d), edge in zip(table, edges)]
        residues = [J]+[emit('*', i, edge, 'residue_difference') for i, edge in enumerate(edges)]
    else:
        offsets = [emit('*', d, edge, 'offset') for (_, d), edge in zip(table, edges)]
        residues = [emit('*', i+1, edge, 'residue') for i, edge in enumerate(edges)]
    next_word = summ([emit('*', baseline, W, 'baseline')]
                    + [emit('*', a-baseline, z, 'slope_difference')
                       for a, z in zip(classes, products)]
                    + offsets,
                    'next_word')
    current_word = summ([emit('*', m, W, 'quotient_scaled')]
                       + residues,
                       'current_word')
    left = emit('+', emit('*', B, next_word, 'shift_next'), 'input', 'transport_left')
    right = emit('+', current_word, emit('*', P, 'target', 'final_target'), 'transport_right')
    bound = summ([J, 'quotient_hat']+[f'product{i}_hat' for i in range(g)]
                 + ['global_slack'], 'global_bound')
    ah = gates.pack(edges+[W]*g+[W], P, 'joined_H')
    am = gates.pack([J]*m+[emit('*', Bm, selector, 'class_mask') for selector in selectors]
                    + [range_mask], P, 'joined_M')
    az = gates.pack(edges+products+[W], P, 'joined_Z')
    exponent, scale = 1, P
    while exponent < m+g+1:
        scale = emit('*', scale, scale, 'scale_power')
        exponent *= 2
    scale = emit('*', B, scale, 'native_scale')
    ns, np, _ = native_host.native.source('and64_prescribed')
    assert ns[:7] == [('q', '*', 16, 'P'), ('scaled_A', '*', 16, 'Hhat'),
        ('padded_A', '-', 'scaled_A', 4), ('scaled_B', '*', 16, 'Mhat'),
        ('padded_B', '-', 'scaled_B', 6), ('scaled_Z', '*', 16, 'Zhat'), ('F3', '-', 'scaled_Z', 8)]
    prefix = 'native__'
    name = lambda value: prefix+value if isinstance(value, str) else value
    source = gates.source+[(prefix+'q', '*', 16, scale),
        (prefix+'scaled_A', '*', 16, ah), (prefix+'padded_A', '+', prefix+'scaled_A', 12),
        (prefix+'scaled_B', '*', 16, am), (prefix+'padded_B', '+', prefix+'scaled_B', 10),
        (prefix+'scaled_Z', '*', 16, az), (prefix+'F3', '+', prefix+'scaled_Z', 8)]
    source += [(name(n), op, name(a), name(b)) for n, op, a, b in ns[7:]]
    auxiliaries = ([f'edge{i}_hat' for i in range(m)]
        + ['quotient_hat', 'height_slack', 'global_slack']
        + [f'product{i}_hat' for i in range(g)]
        + [name(v) for v in native_host.native.domains('and64_prescribed')[1]])
    packet = positive_scale.metadata(dict(source=source,
        comparisons=[(bound, P), (left, right)]+[(name(a), name(b)) for a, b in np],
        parameters=['input', 'target'], auxiliaries=auxiliaries,
        interfaces=dict(h=h, B=B, J=J, P=P, W=W, range_mask=range_mask,
                        next_word=next_word, current_word=current_word,
                        joined_H=ah, joined_M=am, joined_Z=az, native_scale=scale),
        table=table, baseline=baseline, classes=classes, radix_multiplier=K,
        scale_exponent=exponent, form=form, shared_selector_sum=shared_selector_sum))
    positive_scale.checked_source(source, packet['parameters'], auxiliaries)
    if form != 'raw':
        packet = positive_scale.rewrite(packet, prefix)
    if form in ('projected', 'units', 'coupled'):
        packet = fields.rewrite(packet, prefix=prefix)
    if form in ('units', 'coupled'):
        packet = units.rewrite(packet, normalized=True)
    if form == 'coupled':
        packet = coupled.rewrite(packet)
    return packet


def build(table=COLLATZ, form='coupled', baseline='auto', shared_selector_sum=True):
    table = normalize(table)
    assert form in FORMS
    slopes = sorted(set(a for a, _ in table))
    if baseline == 'auto':
        choices = [_build(table, form, slope, shared_selector_sum) for slope in slopes]
        return min(choices, key=lambda p: (p['operations'], p['multiplications'], p['baseline']))
    assert baseline in slopes
    return _build(table, form, baseline, shared_selector_sum)


def polynomial_source(packet, include_empty=False):
    source, out = (units.polynomial_source(packet) if packet.get('native_norm_units')
                   else native_host.polynomial_source(packet))
    if include_empty:
        source += [('empty_difference', '-', 'input', 'target'),
                   ('orbit_output', '*', out, 'empty_difference')]
        out = 'orbit_output'
    return source, out


def ledger(packet, include_empty=False):
    record = units.ledger(packet) if packet.get('native_norm_units') else native_host.ledger(packet)
    parent = record['product'] if packet.get('native_norm_units') else record['polynomial']
    source, out = polynomial_source(packet, include_empty)
    counts = Counter('M' if op == '*' else 'A' for _, op, _, _ in source)
    return dict(certificate=record['certificate'], polynomial=dict(operations=len(source),
        multiplications=counts['M'], additions_subtractions=counts['A'],
        degree_upper_bound=parent['degree_upper_bound']+int(include_empty),
        witnesses=len(packet['auxiliaries']), output=out, includes_empty=include_empty,
        exact_degree_claimed=False))


execute = native_host.execute
at = lambda env, value: env[value] if isinstance(value, str) else value


def direct_outer(packet, values):
    table = packet['table']
    m, g = len(table), len(packet['classes'])
    E = [values[f'edge{i}_hat']-1 for i in range(m)]
    Z = [values[f'product{i}_hat']-1 for i in range(g)]
    J, W = sum(E), values['quotient_hat']-1
    h = values['input']+values['target']+values['height_slack']
    B = packet['radix_multiplier']*h
    P = (B-1)*J+1
    G = [sum(edge for edge, (a, _) in zip(E, table) if a == slope) for slope in packet['classes']]
    R = (h-1)*J
    outgoing = packet['baseline']*W+sum((a-packet['baseline'])*z for a, z in zip(packet['classes'], Z))
    outgoing += sum(d*edge for (_, d), edge in zip(table, E))
    incoming = m*W+sum((i+1)*edge for i, edge in enumerate(E))
    pack = lambda seq: sum(value*P**i for i, value in enumerate(seq))
    H = pack(E+[W]*g+[W])
    M = pack([J]*m+[(B-1)*selector for selector in G]+[R])
    A = pack(E+Z+[W])
    bound = J+values['quotient_hat']+sum(values[f'product{i}_hat'] for i in range(g))+values['global_slack']
    residuals = [bound-P, B*outgoing+values['input']-incoming-P*values['target']]
    return dict(h=h, B=B, J=J, P=P, W=W, range_mask=R, next_word=outgoing,
                current_word=incoming, joined_H=H, joined_M=M, joined_Z=A,
                native_scale=B*P**packet['scale_exponent']), residuals


def pack_path(packet, path):
    assert len(path) >= 2 and all(n > 0 for n in path)
    table = packet['table']
    assert all(step(table, a) == b for a, b in zip(path, path[1:]))
    pairs = [divmod(n-1, len(table)) for n in path[:-1]]
    h = 1
    while h <= max([path[0]+path[-1]]+[q for q, _ in pairs]):
        h *= 2
    B = packet['radix_multiplier']*h
    P = B**len(pairs)
    J = (P-1)//(B-1)
    pack = lambda seq: sum(value*B**i for i, value in enumerate(seq))
    W = pack([q for q, _ in pairs])
    E = [pack([int(r == i) for _, r in pairs]) for i in range(len(table))]
    Z = [pack([q if table[r][0] == slope else 0 for q, r in pairs]) for slope in packet['classes']]
    result = dict(input=path[0], target=path[-1], height_slack=h-path[0]-path[-1],
        quotient_hat=W+1, global_slack=P-J-W-1-sum(Z)-len(Z))
    result.update({f'edge{i}_hat': edge+1 for i, edge in enumerate(E)})
    result.update({f'product{i}_hat': z+1 for i, z in enumerate(Z)})
    assert min(result.values()) > 0
    return result


def raw_audit(packet, cases, seed):
    rng = random.Random(seed)
    source, out = polynomial_source(packet)
    ns, np, _ = native_host.native.source('and64_prescribed')
    for case in range(cases):
        values = {n: rng.randrange(1, 5) if case < cases//2 else rng.randrange(-3, 4)
                  for n in packet['parameters']+packet['auxiliaries']}
        env = execute(source, values)
        oracle, residuals = direct_outer(packet, values)
        assert all(at(env, name) == oracle[key] for key, name in packet['interfaces'].items())
        native_values = dict(P=oracle['native_scale'], Hhat=oracle['joined_H']+1,
            Mhat=oracle['joined_M']+1, Zhat=oracle['joined_Z']+1,
            **{n: values['native__'+n] for n in native_host.native.domains('and64_prescribed')[1]})
        ne = execute(ns, native_values)
        expected = residuals+[at(ne, a)-at(ne, b) for a, b in np]
        assert [at(env, a)-at(env, b) for a, b in packet['comparisons']] == expected
        assert env[out] == sum(r*r for r in expected)
    return dict(full_raw_identities=cases, signed_cases=cases//2)


def path_audit(tables):
    paths = steps = zero_quotient_paths = 0
    for table in tables:
        for baseline in sorted(set(a for a, _ in table)):
            packet = build(table, 'raw', baseline)
            outer = [row for row in packet['source'] if not row[0].startswith('native__')]
            for initial in range(1, 33):
                for length in (1, 2, 4, 7):
                    path = [initial]
                    for _ in range(length):
                        path.append(step(table, path[-1]))
                    values = pack_path(packet, path)
                    oracle, residuals = direct_outer(packet, values)
                    env = execute(outer, values)
                    assert residuals == [0, 0]
                    assert oracle['joined_H'] & oracle['joined_M'] == oracle['joined_Z']
                    assert all(0 <= oracle[n] < oracle['native_scale'] for n in ('joined_H', 'joined_M', 'joined_Z'))
                    assert all(at(env, a) == at(env, b) for a, b in packet['comparisons'][:2])
                    assert all(at(env, name) == oracle[key] for key, name in packet['interfaces'].items())
                    paths += 1; steps += length
                    zero_quotient_paths += values['quotient_hat'] == 1
    assert zero_quotient_paths
    return dict(genuine_paths=paths, chronological_steps=steps, all_zero_quotient_paths=zero_quotient_paths,
        scope='Complete outer rows and joined AND; positive native Pell extension is proved, not materialized.')


def exhaustive_outer_audit():
    table = COLLATZ
    packet = build(table, 'raw')
    h, B = 16, 16*packet['radix_multiplier']
    tested = accepted = corrupted = 0
    for length in (1, 2, 3):
        P = B**length
        J = (P-1)//(B-1)
        for choices in product(range(2), repeat=length):
            E = [sum(B**t for t, r in enumerate(choices) if r == i) for i in range(2)]
            for quotients in product(range(4), repeat=length):
                W = sum(q*B**t for t, q in enumerate(quotients))
                Z = sum(q*B**t for t, (q, r) in enumerate(zip(quotients, choices)) if table[r][0] == packet['classes'][0])
                for x in range(1, 9):
                    for y in range(1, 7):
                        values = dict(input=x, target=y, height_slack=h-x-y,
                            quotient_hat=W+1, product0_hat=Z+1,
                            edge0_hat=E[0]+1, edge1_hat=E[1]+1, global_slack=P-J-W-Z-2)
                        assert min(values.values()) > 0
                        oracle, residuals = direct_outer(packet, values)
                        current = [2*q+r+1 for q, r in zip(quotients, choices)]
                        following = [table[r][0]*q+table[r][1] for q, r in zip(quotients, choices)]
                        legal = current[0] == x and following[-1] == y and following[:-1] == current[1:]
                        assert (residuals == [0, 0]) == legal
                        assert oracle['joined_H'] & oracle['joined_M'] == oracle['joined_Z']
                        tested += 1; accepted += legal
                        if legal:
                            bad = dict(values, product0_hat=values['product0_hat']+1,
                                       global_slack=values['global_slack']-1)
                            assert min(bad.values()) > 0
                            bo, br = direct_outer(packet, bad)
                            assert br[0] == 0 and bo['joined_H'] & bo['joined_M'] != bo['joined_Z']
                            corrupted += 1
    return dict(exhaustive_outer_assignments=tested, valid_paths=accepted,
                corrupted_selected_products_rejected=corrupted)


def closure(packet, include_empty=False):
    source, out = polynomial_source(packet, include_empty)
    nodes = {n: (a, b) for n, _, a, b in source}
    seen, todo = set(), [out]
    while todo:
        value = todo.pop()
        if isinstance(value, str) and value in nodes and value not in seen:
            seen.add(value); todo.extend(nodes[value])
    assert seen == set(nodes)
    return len(source)


def selector_sum_identity_audit(packet, cases, seed):
    """Whole-source equality to the unfactored offset/residue schedule."""
    old = build(packet['table'], packet['form'], packet['baseline'], False)
    assert old['parameters'] == packet['parameters'] and old['auxiliaries'] == packet['auxiliaries']
    before, bo = polynomial_source(old)
    after, ao = polynomial_source(packet)
    rng = random.Random(seed)
    for case in range(cases):
        values = {name: rng.randrange(1, 5) if case < cases//2 else rng.randrange(-3, 4)
                  for name in packet['parameters']+packet['auxiliaries']}
        a, b = execute(before, values), execute(after, values)
        assert a[bo] == b[ao]
        assert all(at(a, old['interfaces'][key]) == at(b, register)
                   for key, register in packet['interfaces'].items())
        assert [at(a, x)-at(a, y) for x, y in old['comparisons']] == [
            at(b, x)-at(b, y) for x, y in packet['comparisons']]
    return dict(complete_output_residual_interface_identities=cases, signed_cases=cases//2)


def verify():
    tables = (COLLATZ, ((2, 3), (2, 2)), ((0, 2), (3, 1), (1, 4)), ((1, 1),))
    ledgers, raws, rewrites, shared_sum = [], [], [], []
    empty_cases = 0
    rng = random.Random(136748)
    for index, table in enumerate(tables):
        for baseline in sorted(set(a for a, _ in table)):
            packets = {form: build(table, form, baseline) for form in FORMS}
            for form, packet in packets.items():
                shared_sum.append(selector_sum_identity_audit(packet, 16, 134700+len(shared_sum)))
                for empty in (False, True):
                    closure(packet, empty)
                    ledgers.append(dict(table=table, baseline=baseline, form=form, **ledger(packet, empty)))
                full, out = polynomial_source(packet, True)
                old, oldout = polynomial_source(packet)
                for case in range(8):
                    values = {n: rng.randrange(1, 4) if case < 4 else rng.randrange(-2, 3)
                              for n in packet['parameters']+packet['auxiliaries']}
                    env = execute(full, values); before = execute(old, values)
                    assert env[out] == (values['input']-values['target'])*before[oldout]
                    empty_cases += 1
            raws.append(raw_audit(packets['raw'], 32, 136800+index))
            rewrites.append(dict(scale=positive_scale.identity_audit(packets['scaled'], 16, 136900+index),
                fields=fields.audit(packets['projected'], 16, 137000+index),
                ordinary_units=units.audit(packets['units']['normalized_parent'], 16, 137100+index),
                normalized_units=units.audit(packets['units'], 16, 137200+index),
                index=coupled.audit(packets['coupled']['coupled_parent'], 16, 137300+index),
                coupled=coupled.audit(packets['coupled'], 16, 137400+index)))
    packet = build()
    source, out = polynomial_source(packet)
    assert ledger(packet)['polynomial']['operations'] == 134
    unfactored = build(shared_selector_sum=False)
    assert ledger(unfactored)['polynomial']['operations'] == 136
    return dict(status='PASS_COMPLETE_RESIDUE_AFFINE_FINITE_HISTORY',
        theorem='For positive input and target, a positive zero exists iff a nonempty finite orbit connects them.',
        default_table=COLLATZ, default_ledger=ledger(packet), empty_orbit_ledger=ledger(packet, True),
        ledgers=ledgers, raw_identities=raws, rewrite_identities=rewrites,
        shared_selector_sum_identities=shared_sum, unfactored_default_ledger=ledger(unfactored),
        empty_orbit_complete_identities=empty_cases, paths=path_audit(tables),
        exhaustive_outer=exhaustive_outer_audit(), source=source, output=out,
        source_sha256=hashlib.sha256(json.dumps(source, separators=(',', ':')).encode()).hexdigest(),
        scope='Generic fixed-table complete history. Shortcut Collatz is not asserted universal; '
              'the prime-coded counter substrate still needs a paid exponent input loader. '
              'No finite orbit experiment is a nontermination claim or a materialized native Pell zero.')


if __name__ == '__main__':
    parser = argparse.ArgumentParser(); parser.add_argument('--write', action='store_true')
    args = parser.parse_args(); result = json.loads(json.dumps(verify()))
    receipt = Path(__file__).with_suffix('.json')
    if args.write:
        receipt.write_text(json.dumps(result, indent=2)+'\n')
    else:
        assert json.loads(receipt.read_text()) == result, 'receipt mismatch'
    print(result['status'])
    print(json.dumps(result['default_ledger'], indent=2))
    print(result['scope'])
