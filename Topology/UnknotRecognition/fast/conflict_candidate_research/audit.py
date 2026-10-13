"""Fresh STANDARD oracles, both candidate policies, and labelled diagram proofs.

No timings are collected. Each supplied source is independently enumerated in
Regina once in this run, then shared by all policy/LP-strategy comparisons.
Retained formal root rays are separately checked at exact labelled successors.
"""
import argparse
from collections import Counter
import json
from pathlib import Path
import platform
import sys

import regina

from fastunknot.integer_codec import json_safe
from fastunknot.normal_crushing_search import recognize_by_crushing
from fastunknot.normal_euler_transversal import search_euler_transversal
from fastunknot.normal_euler_tree_verify import verify_euler_branch_tree
from fastunknot.positive_ray import extract_positive_ray
from normal_crushing_research.fixtures import regina_triangulation
from euler_crushing_research.benchmark import verify_result
from euler_tree_research.audit import (
    standard_oracle, positive_targets, surface_observation, crush_comparison)
from euler_tree_research.fixtures import supplied_cases, diagram_cases
from euler_transversal_research.formal import lower_bound_record
from .common import POLICIES, STRATEGIES, configs, digest, source_hashes, lower_fixtures


def supplied_answer(source, allowed, oracle, targets, policy, strategy):
    result = search_euler_transversal(source, allowed, strategy=strategy,
        candidate_policy=policy, max_hitting_subsets=None)
    expected = 'POSITIVE_EULER' if targets else 'NO_POSITIVE_EULER'
    assert result['status'] == expected, (policy, strategy, result['status'], expected)
    answer = dict(result=result)
    if not targets:
        assert verify_euler_branch_tree(source, result['certificate'])
        answer['independent_tree_replay'] = True
        return answer
    rows = result['coordinates']
    answer['positive_regina'] = surface_observation(source, rows, allowed=allowed)
    assert result['euler_characteristic'] == answer['positive_regina']['euler_characteristic']
    extraction = extract_positive_ray(source, rows)
    answer['extraction'] = extraction
    extracted = extraction['coordinates']
    answer['extracted_regina'] = surface_observation(source, extracted, allowed=allowed)
    assert all(before or not after for original, ray in zip(rows, extracted)
               for before, after in zip(original, ray)), 'extraction grew positive support'
    matching = [vertex['index'] for vertex in oracle['vertices']
                if vertex['coordinates'] == extracted]
    assert len(matching) == 1, 'extracted ray absent from fresh original STANDARD oracle'
    answer['extracted_standard_vertex_index'] = matching[0]
    answer['crushing'] = crush_comparison(source, extracted)
    return answer


def supplied_record(case, oracle):
    targets = positive_targets(oracle, case['allowed_types'])
    return dict(id=case['id'], family=case['family'], mask_bits=case['mask_bits'],
        source_sha256=digest(case['source']), allowed_types=case['allowed_types'],
        oracle_positive=bool(targets), oracle_positive_indices=targets,
        results={policy: {strategy: supplied_answer(case['source'],case['allowed_types'],
            oracle,targets,policy,strategy) for strategy in STRATEGIES} for policy in POLICIES})


def diagram_record(name, diagram, policy, fixture):
    config = configs()[policy]
    result = recognize_by_crushing(diagram, **config)
    replay = verify_result(diagram, result, policy)
    expected = 'UNKNOT' if name == 'circle' else 'KNOTTED'
    assert result['status'] in (expected,'INCONCLUSIVE')
    chain = (result['partial_chain'] if result['status'] == 'INCONCLUSIVE'
             else result['certificate']['chain'])
    source, quotients = chain['shelling']['triangulation'], []
    for packet in chain['steps']:
        observation = surface_observation(source, packet['coordinates'])
        comparison = crush_comparison(source, packet['coordinates'],
            native=dict(status='COMPLETE', certificate=packet))
        quotients.append(dict(source=source, source_sha256=digest(source),
                              positive_regina=observation, crushing=comparison))
        source = packet['successor']
    assert source == chain['triangulation']
    successor, exact_h = None, None
    if source is not None:
        triangulation = regina_triangulation(source)
        successor = dict(tetrahedra=triangulation.size(), vertices=triangulation.countVertices(),
                         valid=triangulation.isValid(), orientable=triangulation.isOrientable())
        assert successor['valid'] and successor['orientable']
        if result['status'] == 'KNOTTED':
            lower = lower_bound_record(source, fixture)
            tree = result['certificate']['exhaustion']
            assert verify_euler_branch_tree(source, tree)
            resolving = sorted({node['tetrahedron'] for node in tree['nodes'] if node['kind'] == 'split'})
            assert len(resolving) == lower['lower_bound']
            exact_h = dict(lower, upper_bound=len(resolving), exact_h=len(resolving),
                resolving_set=resolving, negative_tree_sha256=digest(tree),
                witness_origin='retained rays freshly replayed; no fresh exhaustive root-ray enumeration')
    return dict(id=name, policy=policy, input_pd=[list(row) for row in diagram.pd], config=config,
        result=result, independent_verification=replay, labelled_quotient_comparisons=quotients,
        successor_regina=successor, exact_transversal=exact_h)


def supplied_summary(records, oracles, policy):
    counts = Counter()
    for record in records:
        counts['supplied_positive' if record['oracle_positive'] else 'supplied_negative'] += 1
        for answer in record['results'][policy].values():
            counts['positive_queries' if record['oracle_positive'] else 'negative_queries'] += 1
            counts['supplied_labelled_quotient_equal'] += 'crushing' in answer
            counts['negative_tree_replays'] += answer.get('independent_tree_replay', False)
    counts['oracle_sources'] = len(oracles)
    counts['original_standard_vertices'] = sum(o['standard_vertex_count'] for o in oracles.values())
    return dict(counts)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', required=True)
    parser.add_argument('--supplied-only', action='store_true')
    args = parser.parse_args()
    target = Path(args.output)
    output = dict(passed=False, regina=regina.versionString(), python=sys.version,
        platform=platform.platform(), source_sha256=source_hashes(),
        policies=POLICIES, strategies=STRATEGIES, diagram_configs=configs(),
        scope='fresh original STANDARD vertex comparisons on supplied masks and fresh diagram recognition under both candidate policies; exact labelled quotient comparisons; no timing or general asymptotic claim',
        standard_oracle_origin='fresh Regina NormalCoords.Standard / NormalList.Vertex enumeration in this run',
        lower_ray_origin='retained 19 formal conflict-ray witnesses, freshly checked at matching labelled final sources',
        standard_vertex_oracles={}, supplied=[], diagrams=[])
    def save():
        target.write_text(json.dumps(json_safe(output),indent=2)+'\n')
    save()
    for case in supplied_cases():
        key = digest(case['source'])
        if key not in output['standard_vertex_oracles']:
            output['standard_vertex_oracles'][key] = standard_oracle(case['source'])
        output['supplied'].append(supplied_record(case,output['standard_vertex_oracles'][key]))
        if len(output['supplied']) % 8 == 0:
            save()
            print('supplied',len(output['supplied']),case['id'],flush=True)
    assert len(output['supplied']) == 88
    output['supplied_summaries'] = {policy: supplied_summary(output['supplied'],
        output['standard_vertex_oracles'],policy) for policy in POLICIES}
    save()
    if not args.supplied_only:
        fixtures = {record['id']:record for record in lower_fixtures()}
        for name,diagram in diagram_cases():
            for policy in POLICIES:
                print('diagram_start',name,policy,flush=True)
                output['diagrams'].append(diagram_record(name,diagram,policy,fixtures.get(name)))
                save()
                print('diagram',name,policy,output['diagrams'][-1]['result']['status'],flush=True)
    counts = Counter(supplied_masks=len(output['supplied']),
        supplied_queries=len(output['supplied'])*len(POLICIES)*len(STRATEGIES),
        oracle_sources=len(output['standard_vertex_oracles']),
        original_standard_vertices=sum(o['standard_vertex_count'] for o in output['standard_vertex_oracles'].values()))
    for record in output['diagrams']:
        counts['diagram_'+record['result']['status']] += 1
        counts['diagram_labelled_quotient_equal'] += len(record['labelled_quotient_comparisons'])
        if record['exact_transversal'] is not None:
            counts['exact_transversal_instances'] += 1
            counts['positive_root_ray_replays'] += len(record['exact_transversal']['witness_observations'])
    output['summary'] = dict(counts)
    assert output['source_sha256'] == source_hashes(), 'sources changed during audit'
    output['passed'] = True
    save()
    print('summary',dict(counts),flush=True)


if __name__ == '__main__':
    main()
