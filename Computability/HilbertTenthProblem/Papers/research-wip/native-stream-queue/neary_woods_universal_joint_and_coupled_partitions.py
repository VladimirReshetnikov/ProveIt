"""Exact finite-family degree planning for the coupled two-core U9 source.

Grouping preserves the accepted outer relation, not every supplied
positive zero of the coupled parent. No exact polynomial degree claimed.
"""
import argparse
from functools import lru_cache
import hashlib
import json
from pathlib import Path
import random

import neary_woods_universal_joint_and_coupled as coupled
import neary_woods_universal_joint_and_partitions as partitions

compiler = coupled.compiler
NORMALIZATIONS = partitions.NORMALIZATIONS
EXPECTED_FRONTIER = [(297, 2311), (298, 1543), (299, 1501), (300, 1132),
                     (301, 1092), (302, 756), (303, 730), (304, 608)]


@lru_cache(None)
def build_base(normalized, merge_bound=True):
    assert normalized in NORMALIZATIONS
    old = partitions.build_base(normalized, coupled.PREFIXES, merge_bound)
    return coupled.rewrite(old)


def optimal_partitions(weights, residual):
    """Exhaustive subset DP for the displayed propagated-degree objective.

    opt(mask,k) is the least maximum group sum over exactly k nonempty
    groups partitioning mask. Fixing the least bit in the first group
    removes permutation symmetry. Greedy answers supply only upper bounds;
    pruning uses certified lower bounds and strict-improvement tests.
    """
    assert weights and all(isinstance(w, int) and w > 0 for w in weights)
    assert isinstance(residual, int) and residual >= 0
    n = len(weights)
    size = 1 << n
    sums, largest, cardinality = [0]*size, [0]*size, [0]*size
    for mask in range(1, size):
        bit = mask & -mask
        j, rest = bit.bit_length()-1, mask ^ bit
        sums[mask] = sums[rest]+weights[j]
        largest[mask] = max(largest[rest], weights[j])
        cardinality[mask] = cardinality[rest]+1
    inspected = 0

    @lru_cache(None)
    def opt(mask, k):
        nonlocal inspected
        if k == 0:
            assert mask == 0
            return 0, ()
        if k == 1:
            assert mask
            return sums[mask], (mask,)
        if cardinality[mask] == k:
            return largest[mask], tuple(1 << i for i in range(n) if mask >> i & 1)
        assert 1 < k < cardinality[mask]
        groups, totals = [0]*k, [0]*k
        order = sorted((i for i in range(n) if mask >> i & 1),
                       key=lambda i: (-weights[i], i))
        for i in order:
            j = min(range(k), key=lambda v: (totals[v], v))
            groups[j] |= 1 << i
            totals[j] += weights[i]
        best, chosen = max(totals), tuple(sorted(groups))
        lower = max(largest[mask], (sums[mask]+k-1)//k)
        if best == lower:
            return best, chosen
        first, sub = mask & -mask, mask
        while sub:
            rest = mask ^ sub
            if sub & first and cardinality[rest] >= k-1 and sums[sub] < best:
                inspected += 1
                peak, other_groups = opt(rest, k-1)
                value = max(sums[sub], peak)
                if value < best:
                    best, chosen = value, tuple(sorted((sub,)+other_groups))
                    if best == lower:
                        break
            sub = (sub-1) & mask
        return best, chosen

    full, plans = size-1, []
    for k in range(1, n+1):
        peak, groups = opt(full, k)
        best = 2*max(residual, peak)
        anchor = None
        # Every possible distinguished group is considered. The remaining
        # objective depends only on its optimal maximum group weight.
        for chosen_anchor in range(1, size):
            rest = full ^ chosen_anchor
            if (k == 1 and rest) or (k > 1 and cardinality[rest] < k-1):
                continue
            divisor = max(k-1, 1)
            lower = sums[chosen_anchor]+2*max(
                residual, largest[rest], (sums[rest]+divisor-1)//divisor)
            if lower >= best:
                continue
            peak, others = opt(rest, k-1)
            value = sums[chosen_anchor]+2*max(residual, peak)
            if value < best:
                best, groups, anchor = value, (chosen_anchor,)+others, 0
        partition = [[i for i in range(n) if mask >> i & 1] for mask in groups]
        assert sorted(i for group in partition for i in group) == list(range(n))
        assert len(partition) == k and all(partition)
        degrees = [sum(weights[i] for i in group) for group in partition]
        actual = (2*max([residual]+degrees) if anchor is None else
                  degrees[anchor]+2*max([residual]+[
                      d for j, d in enumerate(degrees) if j != anchor]))
        assert actual == best
        plans.append(dict(groups=k, partition=partition, anchor=anchor,
                          degree_upper_bound=best))
    return plans, dict(memoized_subproblems=opt.cache_info().currsize,
                       evaluated_subset_recurrences=inspected,
                       mask_space=size, factor_count=n)


@lru_cache(None)
def search(normalized):
    packet = build_base(normalized)
    bound = coupled.degree_bound(packet)
    weights = [bound['factor_degree_bounds'][name] for name in packet['unit_factors']]
    plans, statistics = optimal_partitions(weights, bound['maximum_residual_degree_bound'])
    records = []
    for plan in plans:
        rec = partitions.record(packet, plan['partition'], plan['anchor'])
        assert rec['polynomial']['degree_upper_bound'] == plan['degree_upper_bound']
        records.append(rec)
    return dict(normalized_prefixes=normalized, both_cores_indexed_and_coupled=True,
                search_statistics=statistics, best_by_group_count=records)


@lru_cache(None)
def frontier():
    candidates = [r for normalized in NORMALIZATIONS
                  for r in search(normalized)['best_by_group_count']]
    candidates.sort(key=lambda r: (r['polynomial']['operations'],
                                  r['polynomial']['degree_upper_bound']))
    result, least = [], float('inf')
    for record in candidates:
        degree = record['polynomial']['degree_upper_bound']
        if degree < least:
            result.append(record)
            least = degree
    assert [(r['polynomial']['operations'], r['polynomial']['degree_upper_bound'])
            for r in result] == EXPECTED_FRONTIER
    return result


def build(operations=304, *, merge_bound=True):
    """A frontier schedule; default304 has the smallest degree bound608."""
    selected = next(r for r in frontier() if r['polynomial']['operations'] == operations)
    parent = build_base(tuple(selected['normalized_prefixes']), merge_bound)
    packet, _, _ = partitions.source(parent, selected['partition'], selected['anchor'])
    return dict(packet, coupled_partition=True,
                accepted_outer_relation_only=True,
                coupled_partition_record=partitions.record(
                    parent, selected['partition'], selected['anchor']))


def polynomial_source(packet):
    assert packet['coupled_partition']
    compiled, source, out = partitions.source(packet['partition_parent'],
                    packet['factor_partition'], packet['partition_anchor'])
    assert compiled['source'] == packet['source']
    assert compiled['comparisons'] == packet['comparisons']
    return source, out


def degree_bound(packet):
    record = packet['coupled_partition_record']
    return dict(degree_upper_bound=record['polynomial']['degree_upper_bound'],
                exact_degree_claimed=False,
                group_degree_bounds=record['group_degree_bounds'],
                maximum_original_residual_degree_bound=
                    record['maximum_original_residual_degree_bound'])


def small_exhaustive_checks():
    """Independent Bell enumeration validates every g/anchor objective."""
    rng = random.Random(304608)
    cases = enumerated = 0
    for n in range(1, 9):
        for _ in range(3):
            weights = [rng.randrange(1, 31) for _ in range(n)]
            residual = rng.randrange(0, 21)
            best = {}
            for partition in partitions.set_partitions(list(range(n))):
                ds = [sum(weights[i] for i in group) for group in partition]
                values = [2*max([residual]+ds)]+[
                    d+2*max([residual]+[v for j, v in enumerate(ds) if j != k])
                    for k, d in enumerate(ds)]
                g = len(partition)
                best[g] = min(best.get(g, float('inf')), min(values))
                enumerated += 1
            answer, _ = optimal_partitions(weights, residual)
            assert best == {p['groups']: p['degree_upper_bound'] for p in answer}
            cases += 1
    return dict(weighted_search_instances=cases,
                independently_enumerated_small_partitions=enumerated,
                maximum_factors=8)


def verify():
    searches = [search(n) for n in NORMALIZATIONS]
    ledgers, examples = [], []
    for interface in (False, True):
        for study in searches:
            parent = build_base(tuple(study['normalized_prefixes']), interface)
            for choice in study['best_by_group_count']:
                ledgers.append(partitions.record(parent, choice['partition'], choice['anchor']))
        for j, choice in enumerate(frontier()):
            packet = build(choice['polynomial']['operations'], merge_bound=interface)
            rec = dict(packet['coupled_partition_record'])
            parent = packet['partition_parent']
            rec['audit'] = partitions.audit(parent, packet['factor_partition'],
                                            packet['partition_anchor'], 297608+100*interface+j)
            source, out = polynomial_source(packet)
            encoded = compiler.encode_source(source)
            # No dead gate or unbound input is being counted as a useful row.
            nodes = {n: (a, b) for n, _, a, b in source}
            needed = set()
            def visit(name):
                if not isinstance(name, str) or name not in nodes or name in needed:
                    return
                needed.add(name)
                for operand in nodes[name]:
                    visit(operand)
            visit(out)
            assert needed == set(nodes) and len(nodes) == len(source)
            rec.update(source=encoded, output=out, parameters=packet['parameters'],
                       auxiliaries=packet['auxiliaries'],
                       source_sha256=hashlib.sha256(json.dumps(encoded, sort_keys=True).encode()).hexdigest())
            examples.append(rec)
    assert len(ledgers) == 96 and len(examples) == 16
    return dict(status='PASS_NEARY_WOODS_UNIVERSAL_JOINT_AND_COUPLED_PARTITIONS',
                searches=searches, frontier=frontier(), ledgers=ledgers, examples=examples,
                complete_output_checks=64*len(examples), signed_cases=32*len(examples),
                independent_search_validation=small_exhaustive_checks(),
                scope='All four strong-normalization subsets with both cores indexed and coupled; '
                      'exact subset optimization of all disjoint factor partitions and one optional '
                      'unsquared anchor under the displayed propagated degree bounds. '
                      'Every schedule preserves the accepted outer relation and all51 witnesses, '
                      'not necessarily all supplied positive zeros of its coupled parent. '
                      'Both program-bound interfaces are audited. No exact degrees, global circuit '
                      'optimality, or improvement to the separate75/87 route is claimed.')


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
    print(EXPECTED_FRONTIER)
