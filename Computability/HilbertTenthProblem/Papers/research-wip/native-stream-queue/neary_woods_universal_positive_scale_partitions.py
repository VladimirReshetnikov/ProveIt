"""Exact cost/degree planning with independently positive native scales.

The displayed frontier has two objectives, cost and propagated degree;
witness counts vary.  Grouping preserves the accepted outer relation.
"""
import argparse
from functools import lru_cache
import hashlib
import json
from pathlib import Path
import random

import neary_woods_universal_joint_and_coupled_partitions as coupled_partitions
import neary_woods_universal_positive_scale291 as positive_scale

partitions = coupled_partitions.partitions
compiler = coupled_partitions.compiler
NORMALIZATIONS = coupled_partitions.NORMALIZATIONS
SCALE_OPTIONS = NORMALIZATIONS
EXPECTED_FRONTIER = [(291, 3980, 49), (292, 3486, 49), (293, 3440, 49),
                     (294, 2322, 50), (295, 1554, 50), (296, 1508, 50),
                     (297, 1142, 50), (298, 1098, 50), (299, 766, 50),
                     (300, 734, 50), (301, 608, 50)]


@lru_cache(None)
def build_base(normalized, scaled, merge_bound=True):
    assert normalized in NORMALIZATIONS and scaled in SCALE_OPTIONS
    old = coupled_partitions.build_base(normalized, merge_bound)
    packet = positive_scale.rewrite(old, scaled) if scaled else old
    assert packet['witnesses'] == 51-len(scaled)
    return packet


def record(packet, partition, anchor):
    return dict(partitions.record(packet, partition, anchor),
                positive_scale_prefixes=packet.get('positive_scale_prefixes', ()))


@lru_cache(None)
def search(normalized, scaled):
    packet = build_base(normalized, scaled)
    bound = positive_scale.degree_bound(packet)
    weights = [bound['factor_degree_bounds'][name] for name in packet['unit_factors']]
    plans, statistics = coupled_partitions.optimal_partitions(
        weights, bound['maximum_residual_degree_bound'])
    records = []
    for plan in plans:
        rec = record(packet, plan['partition'], plan['anchor'])
        assert rec['polynomial']['degree_upper_bound'] == plan['degree_upper_bound']
        records.append(rec)
    return dict(normalized_prefixes=normalized, positive_scale_prefixes=scaled,
                witnesses=packet['witnesses'], search_statistics=statistics,
                best_by_group_count=records)


@lru_cache(None)
def frontier(witnesses=None):
    assert witnesses in (None, 49, 50, 51)
    candidates = [rec for normalized in NORMALIZATIONS for scaled in SCALE_OPTIONS
                  if witnesses is None or 51-len(scaled) == witnesses
                  for rec in search(normalized, scaled)['best_by_group_count']]
    candidates.sort(key=lambda r: (r['polynomial']['operations'],
                                  r['polynomial']['degree_upper_bound'],
                                  r['certificate']['witnesses']))
    result, least = [], float('inf')
    for rec in candidates:
        degree = rec['polynomial']['degree_upper_bound']
        if degree < least:
            result.append(rec)
            least = degree
    if witnesses is None:
        assert [(r['polynomial']['operations'], r['polynomial']['degree_upper_bound'],
                 r['certificate']['witnesses']) for r in result] == EXPECTED_FRONTIER
    return result


def build(operations=301, *, merge_bound=True, witnesses=None):
    """A cost/degree frontier point, optionally restricted to a witness count."""
    selected = next(r for r in frontier(witnesses)
                    if r['polynomial']['operations'] == operations)
    base = build_base(tuple(selected['normalized_prefixes']),
                      tuple(selected['positive_scale_prefixes']), merge_bound)
    packet, _, _ = partitions.source(base, selected['partition'], selected['anchor'])
    return dict(packet, positive_scale_partition=True,
                accepted_outer_relation_only=True,
                positive_scale_partition_record=record(
                    base, selected['partition'], selected['anchor']))


def polynomial_source(packet):
    assert packet['positive_scale_partition']
    compiled, source, out = partitions.source(packet['partition_parent'],
                    packet['factor_partition'], packet['partition_anchor'])
    assert compiled['source'] == packet['source']
    assert compiled['comparisons'] == packet['comparisons']
    return source, out


def degree_bound(packet):
    rec = packet['positive_scale_partition_record']
    return dict(degree_upper_bound=rec['polynomial']['degree_upper_bound'],
                exact_degree_claimed=False,
                group_degree_bounds=rec['group_degree_bounds'],
                maximum_original_residual_degree_bound=
                    rec['maximum_original_residual_degree_bound'])


def scale_lift_audit(packet, seed):
    assert packet.get('positive_scale_prefixes')
    rng = random.Random(seed)
    for case in range(8):
        pos = case < 4
        draw = lambda: rng.randrange(1, 6) if pos else rng.randrange(-4, 5)
        constants = {n: draw() for n in compiler.NUMERALS}
        if pos:
            constants.update(recoder_radix=4, repunit_divisor=7)
        literal = partitions.parent.constants_parent.materialize_packet(packet, constants)
        values = {n: draw() for n in packet['parameters']+packet['auxiliaries']}
        restored = positive_scale.lift_to_parent(literal, values)
        old = literal['positive_scale_parent']
        rows, output = positive_scale.polynomial_source(literal)
        old_rows, old_output = positive_scale.polynomial_source(old)
        env = compiler.parent.execute(rows, values)
        before = compiler.parent.execute(old_rows, restored)
        changed = {positive_scale.SPECS[p][2] for p in packet['positive_scale_prefixes']}
        assert all(env[n] == before[n] for n, _, _, _ in packet['source'] if n not in changed)
        assert env[output] == before[old_output]
        assert positive_scale.project_from_parent(literal, restored) == values
        if pos:
            assert min(restored.values()) > 0
    return dict(complete_scale_lift_identities=8, signed_cases=4, positive_lifts=4)


def close_source(packet):
    source, output = polynomial_source(packet)
    nodes = {n: (a, b) for n, _, a, b in source}
    needed = set()
    def visit(name):
        if not isinstance(name, str) or name not in nodes or name in needed:
            return
        needed.add(name)
        for operand in nodes[name]:
            visit(operand)
    visit(output)
    assert needed == set(nodes) and len(nodes) == len(source)
    encoded = compiler.encode_source(source)
    return dict(source=encoded, output=output, parameters=packet['parameters'],
                auxiliaries=packet['auxiliaries'],
                source_sha256=hashlib.sha256(json.dumps(encoded, sort_keys=True).encode()).hexdigest())


def degree_floor_audit():
    cases = []
    for normalized in NORMALIZATIONS:
      for scaled in SCALE_OPTIONS:
        packet = build_base(normalized, scaled)
        bound = positive_scale.degree_bound(packet)
        joint = bound['factor_degree_bounds']['and__P17']
        residual = bound['maximum_residual_degree_bound']
        if 'and__' in normalized:
            assert joint >= 708 and residual >= 44
        else:
            assert joint >= 304 and residual >= 206
        assert 2*joint >= 608 and joint+2*residual >= 608
        cases.append(dict(normalized_prefixes=normalized, positive_scale_prefixes=scaled,
                          joint_auxiliary_degree_bound=joint,
                          maximum_residual_degree_bound=residual))
    return dict(bases=cases, minimum_propagated_degree_bound=608,
                scope='Lower bound on the displayed grouping objective, not on actual polynomial degrees.')


def verify():
    searches = [search(n, s) for n in NORMALIZATIONS for s in SCALE_OPTIONS]
    ledgers, examples, off_frontier, lifts = [], [], [], []
    audited = {}
    def plan_key(rec):
        return (rec['bound_is_program_E'], tuple(rec['normalized_prefixes']),
                tuple(rec['positive_scale_prefixes']),
                tuple(tuple(g) for g in rec['partition']), rec['anchor'])
    for interface in (False, True):
        for index, study in enumerate(searches):
            base = build_base(tuple(study['normalized_prefixes']),
                              tuple(study['positive_scale_prefixes']), interface)
            for choice in study['best_by_group_count']:
                ledgers.append(record(base, choice['partition'], choice['anchor']))
            # Every factor separate is strictly off the displayed frontier,
            # and exercises all sixteen bases on both program interfaces.
            partition = [[i] for i in range(len(base['unit_factors']))]
            anchor = 0 if (index+interface) % 2 else None
            rec = record(base, partition, anchor)
            assert rec['polynomial']['operations'] > EXPECTED_FRONTIER[-1][0]
            rec['audit'] = partitions.audit(base, partition, anchor, 301608+100*interface+index)
            off_frontier.append(rec)
            if study['positive_scale_prefixes']:
                lifts.append(scale_lift_audit(base, 291301+100*interface+index))
        for index, choice in enumerate(frontier()):
            packet = build(choice['polynomial']['operations'], merge_bound=interface)
            rec = dict(packet['positive_scale_partition_record'])
            rec['audit'] = partitions.audit(packet['partition_parent'],
                packet['factor_partition'], packet['partition_anchor'], 291608+100*interface+index)
            audited[plan_key(rec)] = rec['audit']
            rec.update(close_source(packet))
            examples.append(rec)
    # Preserve useful49-witness alternatives separately; they do not
    # change the definition or completeness of the two-objective frontier.
    restricted_examples = []
    extra_audits = 0
    for interface in (False, True):
        for index, choice in enumerate(frontier(49)):
            packet = build(choice['polynomial']['operations'], witnesses=49,
                           merge_bound=interface)
            rec = dict(packet['positive_scale_partition_record'])
            key = plan_key(rec)
            reused = key in audited
            if not reused:
                audited[key] = partitions.audit(packet['partition_parent'],
                    packet['factor_partition'], packet['partition_anchor'],
                    493016+100*interface+index)
                extra_audits += 1
            rec.update(audit=audited[key], audit_reused_from_full_frontier=reused)
            rec.update(close_source(packet))
            restricted_examples.append(rec)
    assert len(ledgers) == 384 and len(examples) == 22
    assert len(off_frontier) == 32 and len(lifts) == 24
    assert len(restricted_examples) == 12 and extra_audits == 6
    return dict(status='PASS_NEARY_WOODS_UNIVERSAL_POSITIVE_SCALE_PARTITIONS',
                searches=searches, frontier=frontier(), ledgers=ledgers,
                examples=examples, off_frontier_audits=off_frontier,
                fixed49_frontier=frontier(49), fixed49_sources=restricted_examples,
                complete_grouped_output_checks=64*(len(examples)+len(off_frontier)+extra_audits),
                signed_grouped_output_cases=32*(len(examples)+len(off_frontier)+extra_audits),
                extra_fixed49_schedule_audits=extra_audits,
                complete_scale_lift_checks=8*len(lifts), signed_scale_lift_cases=4*len(lifts),
                scale_lift_audits=lifts, degree_floor=degree_floor_audit(),
                inherited_exact_subset_optimizer='neary_woods_universal_joint_and_coupled_partitions.optimal_partitions',
                scope='Exact cost/propagated-degree frontier across sixteen strong-normalization/positive-scale bases, '
                      'all factor partitions and one optional unsquared anchor. Witness counts vary49..51; this '
                      'is not a three-objective witness Pareto claim. All schedules preserve the complete accepted '
                      'outer relation, not necessarily all positive coupled-parent tuples. Both program interfaces '
                      'remain. No exact degree, unrestricted optimality, or new75/87 bound is claimed.')


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
    print('fixed49', [(r['polynomial']['operations'], r['polynomial']['degree_upper_bound'])
                       for r in result['fixed49_frontier']])
