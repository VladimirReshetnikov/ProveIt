"""Exact finite finalizer planning after the three joined fields are computed.

All sixteen independent strong/positive-scale choices are rebuilt before
grouping.  The objective is the propagated degree bound, not exact degree.
"""
import argparse
from collections import Counter
from functools import lru_cache
import hashlib
import json
from pathlib import Path
import random

import neary_woods_universal_positive_scale_partitions as scales
import neary_woods_universal_loader_scale288 as loader
import neary_woods_universal_mask_gap285 as mask
import neary_woods_universal_duration_floor282 as duration
import neary_woods_universal_computed_ports275 as fields
import neary_woods_universal_factored_ports269 as factored

partitions = scales.partitions
compiler = fields.compiler
execute = fields.execute
NORMALIZATIONS = scales.NORMALIZATIONS
SCALE_OPTIONS = scales.SCALE_OPTIONS
degree_bound = loader.degree_bound
polynomial_source = loader.polynomial_source
EXPECTED = [(275, 3853, 43), (276, 3437, 43), (277, 3391, 43),
            (278, 2273, 44), (279, 1505, 44), (280, 1459, 44),
            (281, 1094, 44), (282, 1048, 44), (283, 734, 44),
            (284, 706, 44), (285, 608, 44)]


@lru_cache(None)
def input_base(normalized, scaled, merge_bound=True):
    """A canonical single-anchor parent, before the field definitions."""
    assert normalized in NORMALIZATIONS and scaled in SCALE_OPTIONS
    original = scales.build_base(normalized, scaled, merge_bound)
    n = len(original['unit_factors'])
    old, _, _ = partitions.source(original, [list(range(n))], 0)
    return duration.rewrite(mask.rewrite(loader.rewrite(old)))


def compute_fields(old):
    """Specialize the fixed outer source on the explicitly enumerated bases.

    This is deliberately not a generic version of the frozen 275 rewrite:
    its whole source and public interface must match one canonical base.
    """
    checked = input_base(tuple(old['normalized_prefixes']),
                         tuple(old.get('positive_scale_prefixes', ())),
                         old['bound_is_program_E'])
    for key in ('source', 'comparisons', 'parameters', 'auxiliaries',
                'unit_factors', 'unit_register', 'unit_product',
                'factor_partition', 'partition_anchor', 'group_products',
                'width', 'interfaces', 'public_registers'):
        assert old.get(key) == checked.get(key), key
    rows = {n: (op, a, b) for n, op, a, b in old['source']}
    expected = {
        'and__input_A': ('+', 'and__F1', 'and__F3'),
        'and__input_B': ('+', 'and__F2', 'and__F3'),
        'and__shared_sum02': ('+', 'and__F0', 'and__F2'),
        'and__bs_Q': ('+', 'and__shared_sum02', 'and__input_A'),
        'and__bs_q': ('-', 'and__q', 'and__bs_Q'),
    }
    assert all(rows[n] == row for n, row in expected.items())
    removed = [('and__input_A', 'and__padded_A'),
               ('and__input_B', 'and__padded_B')]
    assert all(old['comparisons'].count(pair) == 1 for pair in removed)
    assert ('mask_scale', 'scale') in old['comparisons']
    assert ('hist__global_lhs__15', 'hist__P__10') in old['comparisons']
    aliases = {'and__input_A': 'and__padded_A',
               'and__input_B': 'and__padded_B', 'and__bs_q': 1}
    source, simplified = [], []
    for n, op, a, b in old['source']:
        if n in expected:
            continue
        a, b = fields.remap_tree(a, aliases), fields.remap_tree(b, aliases)
        if op == '*' and (a == 1 or b == 1):
            assert n.startswith('partition_product_')
            aliases[n] = b if a == 1 else a
            simplified.append(n)
        else:
            source.append((n, op, a, b))
    source += [('and__F1', '-', 'and__padded_A', 'and__F3'),
               ('and__F2', '-', 'and__padded_B', 'and__F3'),
               ('computed_ports_remaining', '-', 'and__q', 'and__padded_A'),
               ('computed_ports_before_one', '-', 'computed_ports_remaining', 'and__F2'),
               ('and__F0', '-', 'computed_ports_before_one', 1)]
    computed = ['and__F1', 'and__F2', 'and__F0']
    auxiliaries = [n for n in old['auxiliaries'] if n not in computed]
    source = loader.sort_source(source, old['parameters']+auxiliaries)
    pairs = [fields.remap_tree(pair, aliases) for pair in old['comparisons']
             if pair not in removed]
    factors = [n for n in old['unit_factors'] if n != 'and__bs_q']
    anchor = fields.remap_tree(old['unit_register'], aliases)
    count = Counter('M' if op == '*' else 'A' for _, op, _, _ in source)
    packet = dict(old, source=source, comparisons=pairs, auxiliaries=auxiliaries,
        operations=len(source), multiplications=count['M'], additions_subtractions=count['A'],
        equations=len(pairs), witnesses=len(auxiliaries), unit_factors=factors,
        unit_register=anchor, unit_product=True,
        factor_partition=[list(range(len(factors)))], partition_anchor=0,
        group_products=[anchor], computed_joined_input_field=True,
        computed_ports_parent=old, computed_ports_mode='all', computed_fields=computed,
        computed_port_aliases=aliases, simplified_products=simplified,
        removed_port_comparisons=removed, accepted_outer_relation_only=True,
        positive_computed_fields_at_zeros=True, historical_parents_unchanged=True)
    for key in ('interfaces', 'public_registers'):
        if key in old:
            packet[key] = fields.remap_tree(old[key], aliases)
    assert len(simplified) == 1 and len(source) == old['operations']-1
    assert packet['equations'] == old['equations']-2
    assert packet['witnesses'] == old['witnesses']-3
    compiler.check_source(packet)
    return packet


@lru_cache(None)
def build_base(normalized, scaled, merge_bound=True):
    packet = compute_fields(input_base(normalized, scaled, merge_bound))
    assert packet['witnesses'] == 45-len(scaled)
    return packet


def record(base, partition, anchor):
    result = dict(partitions.record(base, partition, anchor),
                  positive_scale_prefixes=base.get('positive_scale_prefixes', ()))
    packet, source, output = partitions.source(base, partition, anchor)
    actual = degree_bound(packet)
    assert actual['degree_upper_bound'] == result['polynomial']['degree_upper_bound']
    assert len(source) == packet['operations']+3*packet['equations']-1
    loader.source_closure(source, output)
    return result


@lru_cache(None)
def search(normalized, scaled):
    base = build_base(normalized, scaled)
    bound = degree_bound(base)
    weights = [bound['factor_degree_bounds'][n] for n in base['unit_factors']]
    plans, statistics = scales.coupled_partitions.optimal_partitions(
        weights, bound['maximum_residual_degree_bound'])
    records = []
    for plan in plans:
        rec = record(base, plan['partition'], plan['anchor'])
        assert rec['polynomial']['degree_upper_bound'] == plan['degree_upper_bound']
        records.append(rec)
    return dict(normalized_prefixes=normalized, positive_scale_prefixes=scaled,
        witnesses=base['witnesses'], search_statistics=statistics,
        best_by_group_count=records)


@lru_cache(None)
def frontier(witnesses=None):
    assert witnesses in (None, 43, 44, 45)
    candidates = [r for n in NORMALIZATIONS for s in SCALE_OPTIONS
                  if witnesses is None or 45-len(s) == witnesses
                  for r in search(n, s)['best_by_group_count']]
    candidates.sort(key=lambda r: (r['polynomial']['operations'],
        r['polynomial']['degree_upper_bound'], r['certificate']['witnesses']))
    result, least = [], float('inf')
    for rec in candidates:
        degree = rec['polynomial']['degree_upper_bound']
        if degree < least:
            result.append(rec)
            least = degree
    return result


def build(operations=275, *, merge_bound=True, witnesses=None):
    selected = next(r for r in frontier(witnesses)
                    if r['polynomial']['operations'] == operations)
    base = build_base(tuple(selected['normalized_prefixes']),
                      tuple(selected['positive_scale_prefixes']), merge_bound)
    packet, _, _ = partitions.source(base, selected['partition'], selected['anchor'])
    return dict(packet, computed_ports_partition=True,
        grouping_preserves_fixed_base_positive_zeros=True,
        computed_ports_partition_record=record(base, selected['partition'], selected['anchor']))


def build_factored(operations=269, *, merge_bound=True, witnesses=None):
    old = build(operations+6, merge_bound=merge_bound, witnesses=witnesses)
    packet = factored.rewrite(old)
    return dict(packet, factored_computed_ports_partition_record=factored_record(
        old['partition_parent'], old['factor_partition'], old['partition_anchor']))


def factored_record(base, partition, anchor):
    rec = record(base, partition, anchor)
    old, _, _ = partitions.source(base, partition, anchor)
    packet = factored.rewrite(old)
    rows, output = polynomial_source(packet)
    count = Counter('M' if op == '*' else 'A' for _, op, _, _ in rows)
    assert degree_bound(packet) == degree_bound(old)
    assert packet['comparisons'] == old['comparisons']
    assert packet['auxiliaries'] == old['auxiliaries']
    assert len(rows) == rec['polynomial']['operations']-6
    loader.source_closure(rows, output)
    return dict(rec, certificate={k: packet[k] for k in rec['certificate']},
        polynomial=dict(rec['polynomial'], operations=len(rows),
            multiplications=count['M'], additions_subtractions=count['A'], output=output),
        factored_ports=True, unfactored_operations=rec['polynomial']['operations'])


@lru_cache(None)
def factored_frontier(witnesses=None):
    return [factored_record(build_base(tuple(r['normalized_prefixes']),
        tuple(r['positive_scale_prefixes'])), r['partition'], r['anchor'])
        for r in frontier(witnesses)]


def summary(records):
    return [(r['polynomial']['operations'], r['polynomial']['degree_upper_bound'],
             r['certificate']['witnesses']) for r in records]


def outer_closure(packet):
    roots = ('and__padded_A', 'and__padded_B', 'and__F3', 'and__q',
             'mask_scale', 'scale', 'hist__global_lhs__15', 'hist__P__10')
    nodes = {n: (op, a, b) for n, op, a, b in packet['source']}
    needed = set()
    def visit(n):
        if not isinstance(n, str) or n not in nodes or n in needed:
            return
        needed.add(n)
        _, a, b = nodes[n]
        visit(a)
        visit(b)
    for n in roots:
        visit(n)
    return sorted((n, *nodes[n]) for n in needed)


def grouped_audit(base, partition, anchor, seed):
    """Evaluate the whole DAG against a separately assembled scalar finalizer."""
    packet, rows, output = partitions.source(base, partition, anchor)
    folded = factored.rewrite(packet)
    folded_rows, folded_output = polynomial_source(folded)
    rng = random.Random(seed)
    for case in range(8):
        positive = case < 4
        draw = lambda: rng.randrange(1, 5) if positive else rng.randrange(-3, 4)
        constants = {n: draw() for n in compiler.NUMERALS}
        if positive:
            constants.update(recoder_radix=4, repunit_divisor=7, history_radix=8)
        values = {n: draw() for n in packet['parameters']+packet['auxiliaries']}
        before = execute(compiler.materialize(base['source'], constants), values)
        after = execute(compiler.materialize(rows, constants), values)
        for n, _, _, _ in partitions.factor_source(base):
            assert before[n] == after[n]
        scalar = lambda v: before[v] if isinstance(v, str) else v
        squared = sum((scalar(a)-scalar(b))**2 for a, b in base['comparisons'][:-1])
        products = []
        for register, group in zip(packet['group_products'], partition):
            product = 1
            for i in group:
                product *= before[base['unit_factors'][i]]
            assert after[register] == product
            products.append(product)
        expected = squared+sum((v-1)**2 for j, v in enumerate(products) if j != anchor)
        if anchor is not None:
            expected = products[anchor]*(1+expected)-1
        assert after[output] == expected
        final = execute(compiler.materialize(folded_rows, constants), values)
        assert final[folded_output] == expected
        assert all(final[n] == after[n] for n in base['unit_factors'])
    return dict(complete_grouped_outputs=8, complete_factored_outputs=8, signed_cases=4)


def source_record(packet):
    rows, output = polynomial_source(packet)
    loader.source_closure(rows, output)
    compiler.check_source(packet)
    assert len(set(packet['auxiliaries'])) == packet['witnesses']
    encoded = compiler.encode_source(rows)
    return dict(source=encoded, output=output, parameters=packet['parameters'],
        auxiliaries=packet['auxiliaries'], source_sha256=hashlib.sha256(
            json.dumps(encoded, sort_keys=True).encode()).hexdigest())


def guards_audit():
    from copy import deepcopy
    original = input_base(NORMALIZATIONS[-1], SCALE_OPTIONS[-1])
    bad = []
    v = deepcopy(original)
    v['source'][0] = (v['source'][0][0], '+', 1, 2)
    bad.append(v)
    v = deepcopy(original)
    v['comparisons'].remove(('mask_scale', 'scale'))
    bad.append(v)
    v = deepcopy(original)
    v['public_registers'] = dict(v.get('public_registers', {}), extra='and__F0')
    bad.append(v)
    v = deepcopy(original)
    v['interfaces'] = dict(v.get('interfaces', {}), nested=['and__bs_q', None])
    bad.append(v)
    v = deepcopy(original)
    v['group_products'] = ['and__F0']
    bad.append(v)
    for value in bad:
        try:
            compute_fields(value)
        except AssertionError:
            pass
        else:
            raise AssertionError('modified canonical base accepted')
    return dict(rejected_modified_bases=len(bad))


def degree_floor_audit():
    cases = []
    for normalized in NORMALIZATIONS:
      for scaled in SCALE_OPTIONS:
        b = build_base(normalized, scaled)
        d = degree_bound(b)
        factor = d['factor_degree_bounds']['and__P17']
        residual = d['maximum_residual_degree_bound']
        if 'and__' in normalized:
            assert factor >= 708
        else:
            assert factor >= 304 and residual >= 206
        assert 2*factor >= 608 and factor+2*residual >= 608
        cases.append(dict(normalized_prefixes=normalized, positive_scale_prefixes=scaled,
                          joint_auxiliary_degree_bound=factor,
                          maximum_residual_degree_bound=residual))
    return dict(bases=cases, minimum_objective=608,
        scope='Lower bound only for the stated propagated grouping objective.')


def verify():
    studies = [search(n, s) for n in NORMALIZATIONS for s in SCALE_OPTIONS]
    assert summary(frontier()) == EXPECTED
    records, folded_records, off_frontier, bases, examples, folded_examples = [], [], [], [], [], []
    for interface in (False, True):
        reference = outer_closure(input_base(NORMALIZATIONS[-1], SCALE_OPTIONS[-1], interface))
        for j, study in enumerate(studies):
            n, s = tuple(study['normalized_prefixes']), tuple(study['positive_scale_prefixes'])
            base = build_base(n, s, interface)
            assert outer_closure(base) == reference
            # A complete integer graph identity against the separately
            # executed, unspecialized three-field parent, on every base.
            graph = fields.audit(base, 275160+len(bases))
            bases.append(dict(normalized_prefixes=n, positive_scale_prefixes=s,
                bound_is_program_E=interface, witnesses=base['witnesses'],
                degree=degree_bound(base), outer_source=compiler.encode_source(reference),
                graph_audit=graph))
            for plan in study['best_by_group_count']:
                rec = record(base, plan['partition'], plan['anchor'])
                rec['audit'] = grouped_audit(base, plan['partition'], plan['anchor'],
                                            2751000+len(records))
                records.append(rec)
                folded_records.append(factored_record(base, plan['partition'], plan['anchor']))
            # Both finalizers on two independent, nonoptimized partitions.
            count = len(base['unit_factors'])
            rng = random.Random(2759000+j)
            order = list(range(count))
            rng.shuffle(order)
            groups = [order[::3], order[1::3], order[2::3]]
            for anchor in (None, 1):
                rec = record(base, groups, anchor)
                rec['audit'] = grouped_audit(base, groups, anchor, 2758000+len(off_frontier))
                off_frontier.append(rec)
        seen = set()
        for witnesses in (None, 43, 44, 45):
            for plan in frontier(witnesses):
                packet = build(plan['polynomial']['operations'], merge_bound=interface,
                               witnesses=witnesses)
                key = (tuple(packet['normalized_prefixes']),
                       tuple(packet.get('positive_scale_prefixes', ())),
                       tuple(tuple(g) for g in packet['factor_partition']),
                       packet['partition_anchor'])
                if key in seen:
                    continue
                seen.add(key)
                examples.append(dict(packet['computed_ports_partition_record'],
                                     **source_record(packet)))
                folded = build_factored(plan['polynomial']['operations']-6,
                    merge_bound=interface, witnesses=witnesses)
                folded_examples.append(dict(folded['factored_computed_ports_partition_record'],
                                             **source_record(folded)))
    assert len(records) == 352 and len(bases) == 32 and len(off_frontier) == 64
    return dict(status='PASS_NEARY_WOODS_UNIVERSAL_COMPUTED_PORTS_PARTITIONS',
        frontier=EXPECTED,
        factored_frontier=summary(factored_frontier()),
        witness_frontiers={str(w): summary(frontier(w)) for w in (43, 44, 45)},
        factored_witness_frontiers={str(w): summary(factored_frontier(w)) for w in (43, 44, 45)},
        searches=studies, ledgers=records, factored_ledgers=folded_records,
        bases=bases, off_frontier=off_frontier, examples=examples, factored_examples=folded_examples,
        degree_floor=degree_floor_audit(), guards=guards_audit(),
        complete_grouped_outputs=8*(len(records)+len(off_frontier)),
        identical_factored_grouped_outputs=8*(len(records)+len(off_frontier)),
        signed_grouped_cases=4*(len(records)+len(off_frontier)),
        whole_three_field_lift_identities=32*len(bases),
        signed_field_lift_cases=16*len(bases),
        scope='Exact finite optimum for 16 fixed strong/scale sources, every factor partition, '
              'and SOS or one unsquared group. Accepted valid-program ordinary-input relation '
              'is preserved; neither arbitrary-parent-tuple equivalence nor exact degrees are claimed.')


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
