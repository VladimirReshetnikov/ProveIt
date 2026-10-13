"""Fresh original-STANDARD oracle, labelled crushing, and exact finite h audit.

No timing measurements are recorded. Regina enumerates each original supplied
source afresh; retained conflict rays are separately replayed on the exact
labelled endpoint of a fresh authenticated diagram-driver run.
"""
import argparse
from collections import Counter
import json
from pathlib import Path
import platform
import sys

import regina

from fastunknot.integer_codec import json_safe
from fastunknot.normal_crushing_search import recognize_by_crushing, verify_crushing_recognition
from fastunknot.normal_euler_transversal import search_euler_transversal
from fastunknot.normal_euler_tree_verify import verify_euler_branch_tree
from fastunknot.positive_ray import extract_positive_ray
from normal_crushing_research.fixtures import regina_triangulation
from euler_tree_research.audit import (
    standard_oracle, positive_targets, surface_observation, crush_comparison)
from euler_tree_research.fixtures import supplied_cases, diagram_cases
from .common import STRATEGIES, DIAGRAM_CONFIG, digest, source_hashes, lower_fixtures
from .formal import lower_bound_record


def supplied_record(case, oracle):
    source, allowed = case['source'], case['allowed_types']
    targets = positive_targets(oracle, allowed)
    record = dict(id=case['id'], family=case['family'], source_sha256=digest(source),
                  mask_bits=case['mask_bits'], allowed_types=allowed,
                  oracle_positive=bool(targets), oracle_positive_indices=targets, results={})
    for strategy in STRATEGIES:
        result = search_euler_transversal(source, allowed, strategy=strategy)
        expected = 'POSITIVE_EULER' if targets else 'NO_POSITIVE_EULER'
        assert result['status'] == expected, (case['id'], strategy, result['status'], expected)
        answer = dict(result=result)
        if targets:
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
            assert len(matching) == 1, 'extracted ray absent from fresh original standard oracle'
            answer['extracted_standard_vertex_index'] = matching[0]
            answer['crushing'] = crush_comparison(source, extracted)
        else:
            assert verify_euler_branch_tree(source, result['certificate'])
            answer['independent_tree_replay'] = True
        record['results'][strategy] = answer
    return record


def diagram_record(name, diagram, fixtures):
    result = recognize_by_crushing(diagram, **DIAGRAM_CONFIG)
    expected = 'UNKNOT' if name == 'circle' else 'KNOTTED'
    assert result['status'] == expected, (name, result['status'], result.get('reason'))
    assert verify_crushing_recognition(diagram, result['certificate'])
    chain = result['certificate']['chain']
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
        fixture = fixtures[name]
        lower = lower_bound_record(source, fixture)
        tree = result['certificate']['exhaustion']
        assert verify_euler_branch_tree(source, tree)
        B = sorted({node['tetrahedron'] for node in tree['nodes'] if node['kind'] == 'split'})
        assert len(B) == lower['lower_bound']
        exact_h = dict(lower, upper_bound=len(B), exact_h=len(B), resolving_set=B,
                       negative_tree_sha256=digest(tree),
                       witness_origin='retained rays freshly replayed; no fresh exhaustive root-ray enumeration')
    return dict(id=name, input_pd=[list(row) for row in diagram.pd], config=DIAGRAM_CONFIG,
                result=result, independent_verification='recognition',
                labelled_quotient_comparisons=quotients, successor_regina=successor,
                exact_transversal=exact_h)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', required=True)
    parser.add_argument('--supplied-only', action='store_true')
    args = parser.parse_args()
    output = dict(passed=False, regina=regina.versionString(), python=sys.version,
        platform=platform.platform(), source_sha256=source_hashes(),
        scope='finite fresh original-STANDARD vertex comparisons, full-ray labelled crushing comparisons, and fresh diagram-bound recognition; no timing or asymptotic claim',
        standard_oracle_origin='fresh Regina NormalCoords.Standard / NormalList.Vertex enumeration in this run',
        lower_ray_origin='retained conflict-ray fixtures, freshly checked only at matching final labelled diagram sources',
        strategies=STRATEGIES, diagram_config=DIAGRAM_CONFIG,
        standard_vertex_oracles={}, supplied=[], diagrams=[])
    target = Path(args.output)
    def save():
        target.write_text(json.dumps(json_safe(output), indent=2)+'\n')
    save()
    for case in supplied_cases():
        key = digest(case['source'])
        if key not in output['standard_vertex_oracles']:
            output['standard_vertex_oracles'][key] = standard_oracle(case['source'])
        output['supplied'].append(supplied_record(case, output['standard_vertex_oracles'][key]))
        if len(output['supplied']) % 8 == 0:
            save()
            print('supplied', len(output['supplied']), case['id'], flush=True)
    assert len(output['supplied']) == 88
    save()
    if not args.supplied_only:
        fixtures = {item['id']: item for item in lower_fixtures()}
        for name, diagram in diagram_cases():
            print('diagram_start', name, flush=True)
            output['diagrams'].append(diagram_record(name, diagram, fixtures))
            save()
            print('diagram', name, output['diagrams'][-1]['result']['status'], flush=True)
    counts = Counter()
    for record in output['supplied']:
        counts['supplied_positive' if record['oracle_positive'] else 'supplied_negative'] += 1
        for strategy in STRATEGIES:
            answer = record['results'][strategy]
            counts['positive_queries' if record['oracle_positive'] else 'negative_queries'] += 1
            counts['supplied_labelled_quotient_equal'] += 'crushing' in answer
            counts['negative_tree_replays'] += answer.get('independent_tree_replay', False)
    for record in output['diagrams']:
        counts['diagram_'+record['result']['status']] += 1
        counts['diagram_labelled_quotient_equal'] += len(record['labelled_quotient_comparisons'])
        if record['exact_transversal'] is not None:
            counts['exact_transversal_instances'] += 1
            counts['positive_root_ray_replays'] += len(record['exact_transversal']['witness_observations'])
    counts['oracle_sources'] = len(output['standard_vertex_oracles'])
    counts['original_standard_vertices'] = sum(o['standard_vertex_count'] for o in output['standard_vertex_oracles'].values())
    output['summary'] = dict(counts)
    assert output['source_sha256'] == source_hashes(), 'audited sources changed during run'
    output['passed'] = True
    save()
    print('summary', dict(counts), flush=True)


if __name__ == '__main__':
    main()
