"""Operation/degree tradeoffs for the complete two-core U9 polynomial.

Enumerate factor partitions, with either an ordinary SOS or one unsquared
unit-product group. Bounds are conservative; the finite search concerns
only this specified family of finalizers.
"""
import argparse
from collections import Counter
from functools import lru_cache
import hashlib
import json
from pathlib import Path
import random

import neary_woods_universal_joint_and_units as parent
import neary_woods_universal_joint_and_arithmetic as indices
from complete75_norm_product91 import set_partitions

compiler = parent.compiler
NORMALIZATIONS = ((), ('geo__',), ('and__',), parent.PREFIXES)
INDEX_OPTIONS = NORMALIZATIONS


@lru_cache(None)
def build_base(normalized=parent.PREFIXES, indexed=(), merge_bound=True):
    assert normalized in NORMALIZATIONS
    assert indexed in INDEX_OPTIONS
    original = parent.build('units', merge_bound=merge_bound)
    # The parent's full normalization supplies the dependency audit for
    # rebuilding either core's five canonical auxiliaries independently.
    parent.normalize(original)
    packet = original
    for prefix in normalized:
        packet = parent.strong.rewrite(dict(packet, core_prefix=prefix, scale_exponent=1))
    if indexed:
        packet = indices.rewrite(dict(packet, form='normalized' if normalized else 'units'), indexed)
    packet = dict(packet, form='partition_base', normalized_prefixes=normalized,
                  indexed_prefixes=indexed)
    for key in ('exact_degree', 'alternative_SOS_degree', 'scale_exponent'):
        packet.pop(key, None)
    compiler.check_source(packet)
    return packet


def factor_source(packet):
    """Retain exactly the closure of factors and ordinary comparisons."""
    assert packet['comparisons'][-1] == (packet['unit_register'], 1)
    nodes = {n: (op, a, b) for n, op, a, b in packet['source']}
    inputs = set(packet['parameters']+packet['auxiliaries'])
    needed = set()

    def visit(n):
        if not isinstance(n, str) or n in inputs or n in needed:
            return
        op, a, b = nodes[n]
        visit(a)
        visit(b)
        needed.add(n)

    for n in packet['unit_factors']:
        visit(n)
    for a, b in packet['comparisons'][:-1]:
        visit(a)
        visit(b)
    source = [row for row in packet['source'] if row[0] in needed]
    assert len(source) == packet['operations']-len(packet['unit_factors'])+1
    return source


def source(packet, partition, anchor):
    factors = packet['unit_factors']
    assert sorted(i for group in partition for i in group) == list(range(len(factors)))
    assert all(group for group in partition)
    assert anchor is None or 0 <= anchor < len(partition)
    certificate = factor_source(packet)
    products = []
    for j, group in enumerate(partition):
        last = factors[group[0]]
        for k, i in enumerate(group[1:]):
            nxt = f'partition_product_{j}_{k}'
            certificate.append((nxt, '*', last, factors[i]))
            last = nxt
        products.append(last)
    ordinary = list(packet['comparisons'][:-1])
    pairs = ordinary+[(v, 1) for j, v in enumerate(products) if j != anchor]
    polynomial = list(certificate)
    last = None
    for j, (a, b) in enumerate(pairs):
        r, s = f'partition_residual_{j}', f'partition_square_{j}'
        polynomial.extend(((r, '-', a, b), (s, '*', r, r)))
        if last is None:
            last = s
        else:
            nxt = f'partition_sum_{j}'
            polynomial.append((nxt, '+', last, s))
            last = nxt
    assert last is not None
    if anchor is not None:
        polynomial.extend((('partition_positive', '+', last, 1),
                           ('partition_scaled', '*', products[anchor], 'partition_positive'),
                           ('partition_output', '-', 'partition_scaled', 1)))
        last = 'partition_output'
    all_pairs = pairs+([(products[anchor], 1)] if anchor is not None else [])
    cc = Counter('M' if op == '*' else 'A' for _, op, _, _ in certificate)
    compiled = dict(packet, source=certificate, comparisons=all_pairs,
                    operations=len(certificate), multiplications=cc['M'],
                    additions_subtractions=cc['A'], equations=len(all_pairs),
                    partition_parent=packet, factor_partition=partition,
                    partition_anchor=anchor, group_products=products,
                    unit_register=products[anchor] if anchor is not None else None,
                    unit_product=anchor is not None)
    compiler.check_source(compiled)
    n, m, g = len(factors), len(ordinary), len(partition)
    expected = len(factor_source(packet))+n+3*m-1+2*g
    assert len(polynomial) == expected
    # Both finalizers have this cost; only their degree formulas differ.
    return compiled, polynomial, last


def record(packet, partition, anchor):
    compiled, polynomial, output = source(packet, partition, anchor)
    bound = parent.degree_bound(packet)
    degrees = [bound['factor_degree_bounds'][n] for n in packet['unit_factors']]
    group_degrees = [sum(degrees[i] for i in group) for group in partition]
    residual = bound['maximum_residual_degree_bound']
    if anchor is None:
        degree = 2*max([residual]+group_degrees)
    else:
        degree = group_degrees[anchor]+2*max([residual]+[
            d for j, d in enumerate(group_degrees) if j != anchor])
    pc = Counter('M' if op == '*' else 'A' for _, op, _, _ in polynomial)
    return dict(normalized_prefixes=packet['normalized_prefixes'],
                indexed_prefixes=packet['indexed_prefixes'],
                bound_is_program_E=packet['bound_is_program_E'],
                partition=partition, anchor=anchor,
                factor_names=packet['unit_factors'], factor_degree_bounds=degrees,
                group_degree_bounds=group_degrees,
                maximum_original_residual_degree_bound=residual,
                certificate={k: compiled[k] for k in ('operations', 'multiplications',
                    'additions_subtractions', 'equations', 'witnesses')},
                polynomial=dict(operations=len(polynomial), multiplications=pc['M'],
                    additions_subtractions=pc['A'], output=output,
                    degree_upper_bound=degree, exact_degree_claimed=False))


def search(normalized, indexed):
    packet = build_base(normalized, indexed)
    bound = parent.degree_bound(packet)
    degrees = list(bound['factor_degree_bounds'].values())
    residual = bound['maximum_residual_degree_bound']
    best, count = {}, 0
    for partition in set_partitions(list(range(len(degrees)))):
        count += 1
        sums = [sum(degrees[i] for i in group) for group in partition]
        choices = [(2*max([residual]+sums), None)]+[
            (d+2*max([residual]+[v for j, v in enumerate(sums) if j != i]), i)
            for i, d in enumerate(sums)]
        degree, anchor = min(choices, key=lambda v: v[0])
        g = len(partition)
        if g not in best or degree < best[g][0]:
            best[g] = degree, partition, anchor
    expected_partitions = {7: 877, 8: 4140, 9: 21147, 10: 115975, 11: 678570}
    assert count == expected_partitions[len(degrees)]
    records = [record(packet, partition, anchor) for _, partition, anchor in best.values()]
    records.sort(key=lambda r: r['polynomial']['operations'])
    return dict(normalized_prefixes=normalized, indexed_prefixes=indexed,
                enumerated_partitions=count, best_by_group_count=records)


def audit(packet, partition, anchor, seed):
    compiled, polynomial, output = source(packet, partition, anchor)
    rng = random.Random(seed)
    for case in range(64):
        positive = case < 32
        numerals = {n: rng.randrange(1, 8) if positive else rng.randrange(-5, 6)
                    for n in compiler.NUMERALS}
        if positive:
            numerals.update(recoder_radix=4, repunit_divisor=7)
        old = parent.constants_parent.materialize_packet(packet, numerals)
        new = parent.constants_parent.materialize_packet(compiled, numerals)
        literal = compiler.materialize(polynomial, numerals)
        values = {n: rng.randrange(1, 5) if positive else rng.randrange(-3, 4)
                  for n in packet['parameters']+packet['auxiliaries']}
        before = compiler.parent.execute(old['source'], values)
        after = compiler.parent.execute(new['source'], values)
        assert all(after[n] == before[n] for n, _, _, _ in factor_source(packet))
        scalar = compiler.parent.scalar
        squared = sum((scalar(a, before)-scalar(b, before))**2
                      for a, b in packet['comparisons'][:-1])
        products = []
        for group in partition:
            product = 1
            for i in group:
                product *= before[packet['unit_factors'][i]]
            products.append(product)
        expected = squared+sum((p-1)**2 for j, p in enumerate(products) if j != anchor)
        if anchor is not None:
            expected = products[anchor]*(1+expected)-1
        assert compiler.parent.execute(literal, values)[output] == expected
    return dict(complete_output_checks=64, signed_cases=32)


def verify():
    searches = [search(normalized, indexed) for normalized in NORMALIZATIONS for indexed in INDEX_OPTIONS]
    candidates = [r for s in searches for r in s['best_by_group_count']]
    candidates.sort(key=lambda r: (r['polynomial']['operations'], r['polynomial']['degree_upper_bound']))
    frontier, smallest = [], float('inf')
    for r in candidates:
        degree = r['polynomial']['degree_upper_bound']
        if degree < smallest:
            frontier.append(r)
            smallest = degree
    assert [(r['polynomial']['operations'], r['polynomial']['degree_upper_bound']) for r in frontier] == [
        (301, 2475), (302, 1707), (303, 1522), (304, 1296),
        (305, 1144), (307, 1110), (308, 1076)]
    assert sum(s['enumerated_partitions'] for s in searches) == 1286789
    examples = []
    for interface in (False, True):
        for j, r in enumerate(frontier):
            packet = build_base(tuple(r['normalized_prefixes']), tuple(r['indexed_prefixes']), interface)
            rec = record(packet, r['partition'], r['anchor'])
            rec['audit'] = audit(packet, r['partition'], r['anchor'], 3031076+100*interface+j)
            _, polynomial, out = source(packet, r['partition'], r['anchor'])
            encoded = compiler.encode_source(polynomial)
            rec.update(source=encoded, output=out,
                       source_sha256=hashlib.sha256(json.dumps(encoded, sort_keys=True).encode()).hexdigest(),
                       parameters=packet['parameters'], auxiliaries=packet['auxiliaries'])
            examples.append(rec)
    return dict(status='PASS_NEARY_WOODS_UNIVERSAL_JOINT_AND_PARTITIONS',
                searches=searches, frontier=frontier, examples=examples,
                complete_output_checks=128*len(frontier), signed_cases=64*len(frontier),
                scope='All sixteen subsets of the two existing strong normalizations and index units; '
                      'all factor partitions and one optional unsquared anchor. '
                      'Optimality applies only to propagated degree bounds in this family. '
                      'The complete positive outer relation is unchanged; all51 witnesses '
                      'and both program interfaces remain. No exact degrees claimed.')


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
    print([(r['polynomial']['operations'], r['polynomial']['degree_upper_bound']) for r in result['frontier']])
