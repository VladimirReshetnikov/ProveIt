"""Fresh original-standard Regina audit of Q-mask trees and diagram chains.

Run from fast/: python -B -m euler_tree_research.audit --output PATH
Every finite supplied query runs both source/restricted models and both Euler
strategies. Diagram queries use finite shared allowances; unfinished queries
retain independently checked partial chains and are never labelled negative.
This correctness audit records no timing measurements.
"""
import argparse
from collections import Counter
from hashlib import sha256
import json
from pathlib import Path
import platform
import sys

import regina

from fastunknot.integer_codec import json_safe
from fastunknot.normal_crushing import crush_normal_ray
from fastunknot.normal_crushing_chain import verify_crushing_chain
from fastunknot.normal_crushing_search import recognize_by_crushing, verify_crushing_recognition
from fastunknot.normal_crushing_verify import verify_normal_crushing
from fastunknot.normal_euler_tree import search_euler_tree
from fastunknot.normal_euler_tree_verify import verify_euler_branch_tree
from fastunknot.positive_ray import extract_positive_ray
from normal_crushing_research.fixtures import regina_triangulation, coordinates
from normal_crushing_research.oracle import inspect
from .benchmark import source_hashes
from .fixtures import supplied_cases, diagram_cases


MODELS = ('source', 'restricted')
STRATEGIES = ('envelope', 'anchors')
DIAGRAM_CONFIG = dict(sector_method='tree', tree_model='source', lp_strategy='envelope',
                      reduce_vertices=True, max_tree_nodes=256,
                      max_pivots=10000, max_anchors=10000, max_crushes=None)


def digest(value):
    return sha256(json.dumps(value, sort_keys=True, separators=(',', ':')).encode()).hexdigest()


def standard_oracle(source):
    """Fresh enumeration on original standard matching, without Q parameters."""
    triangulation = regina_triangulation(source)
    assert triangulation.isValid() and triangulation.isOrientable()
    surfaces = regina.NormalSurfaces(triangulation, regina.NormalCoords.Standard,
                                    regina.NormalList.Vertex)
    vertices = []
    for index, surface in enumerate(surfaces):
        rows = coordinates(surface, triangulation)
        vertices.append(dict(index=index, coordinates=rows,
            euler_characteristic=int(str(surface.eulerChar())),
            vertex_link=surface.isVertexLinking(), connected=surface.isConnected(),
            quad_support=[[t, q] for t, row in enumerate(rows) for q in range(3) if row[4+q]]))
    return dict(source=source, standard_vertex_count=len(vertices), vertices=vertices,
                vertex_count=triangulation.countVertices(),
                boundary_vertex_count=sum(vertex.isBoundary() for vertex in triangulation.vertices()))


def positive_targets(oracle, mask):
    allowed = set(map(tuple, mask))
    return [vertex['index'] for vertex in oracle['vertices']
            if vertex['euler_characteristic'] > 0 and not vertex['vertex_link']
            and vertex['quad_support']
            and all(tuple(pair) in allowed for pair in vertex['quad_support'])]


def surface_observation(source, rows, *, allowed=None):
    """Check original standard matching and canonicality independently."""
    triangulation = regina_triangulation(source)
    flat = [value for row in rows for value in row]
    assert len(rows) == triangulation.size() and all(len(row) == 7 for row in rows)
    assert all(type(value) is int and value >= 0 for value in flat)
    equations = regina.makeMatchingEquations(triangulation, regina.NormalCoords.Standard)
    for i in range(equations.rows()):
        assert sum(int(str(equations.entry(i, j)))*value for j, value in enumerate(flat)) == 0
    support = [[t, q] for t, row in enumerate(rows) for q in range(3) if row[4+q]]
    assert support and all(sum(bool(value) for value in row[4:]) <= 1 for row in rows)
    if allowed is not None:
        assert set(map(tuple, support)) <= set(map(tuple, allowed))
    minima = {}
    for t, tetrahedron in enumerate(triangulation.tetrahedra()):
        for vertex in range(4):
            global_vertex = tetrahedron.vertex(vertex).index()
            minima[global_vertex] = min(minima.get(global_vertex, rows[t][vertex]), rows[t][vertex])
    assert not any(minima.values())
    surface = regina.NormalSurface(triangulation, regina.NormalCoords.Standard, flat)
    observation = dict(euler_characteristic=int(str(surface.eulerChar())),
                       connected=surface.isConnected(), vertex_link=surface.isVertexLinking(),
                       quad_support=support, vertex_triangle_minima=sorted(minima.items()))
    assert observation['euler_characteristic'] > 0 and not observation['vertex_link']
    return observation


def crush_comparison(source, rows, *, native=None):
    oracle = inspect(source, rows)
    assert oracle['eligible'] and oracle['connected'] and oracle['support_nullity'] == 1
    result = crush_normal_ray(source, rows) if native is None else native
    assert result['status'] == 'COMPLETE'
    packet = result['certificate']
    assert packet['coordinates'] == rows and verify_normal_crushing(source, packet)
    for actual, expected in (('triangulation', 'quotient'), ('components', 'components'),
                             ('torus_component', 'torus_component'), ('successor', 'successor')):
        assert packet[actual] == oracle[expected], actual
    return dict(native=result, regina=oracle, independent_crushing_replay=True,
                exact_labelled_quotient_equal=True)


def supplied_record(case, oracle):
    source, allowed = case['source'], case['allowed_types']
    targets = positive_targets(oracle, allowed)
    record = dict(id=case['id'], family=case['family'], source_sha256=digest(source),
                  mask_bits=case['mask_bits'], allowed_types=allowed,
                  oracle_positive=bool(targets), oracle_positive_indices=targets, results={})
    for model in MODELS:
        record['results'][model] = {}
        for strategy in STRATEGIES:
            result = search_euler_tree(source, allowed, model=model, strategy=strategy)
            expected = 'POSITIVE_EULER' if targets else 'NO_POSITIVE_EULER'
            assert result['status'] == expected, (case['id'], model, strategy, result['status'], expected)
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
                assert len(matching) == 1, 'extracted ray absent from original standard vertex oracle'
                answer['extracted_standard_vertex_index'] = matching[0]
                answer['crushing'] = crush_comparison(source, extracted)
            else:
                assert verify_euler_branch_tree(source, result['certificate'])
                answer['independent_tree_replay'] = True
            record['results'][model][strategy] = answer
    return record


def diagram_record(name, diagram):
    result = recognize_by_crushing(diagram, **DIAGRAM_CONFIG)
    status = result['status']
    if status == 'INCONCLUSIVE':
        chain = result['partial_chain']
        assert 'certificate' not in result and verify_crushing_chain(diagram, chain)
        verification = 'partial_chain'
    else:
        assert status in ('UNKNOT', 'KNOTTED')
        assert verify_crushing_recognition(diagram, result['certificate'])
        chain = result['certificate']['chain']
        verification = 'recognition'
    source = chain['shelling']['triangulation']
    quotients = []
    for packet in chain['steps']:
        rows = packet['coordinates']
        observation = surface_observation(source, rows)
        comparison = crush_comparison(source, rows,
            native=dict(status='COMPLETE', certificate=packet))
        quotients.append(dict(source=source, source_sha256=digest(source),
                              positive_regina=observation, crushing=comparison))
        source = packet['successor']
    assert source == chain['triangulation']
    successor = None
    if source is not None:
        triangulation = regina_triangulation(source)
        successor = dict(tetrahedra=triangulation.size(), vertices=triangulation.countVertices(),
                          valid=triangulation.isValid(), orientable=triangulation.isOrientable())
        assert successor['valid'] and successor['orientable']
    return dict(id=name, input_pd=[list(row) for row in diagram.pd], config=DIAGRAM_CONFIG,
                result=result, independent_verification=verification,
                labelled_quotient_comparisons=quotients, successor_regina=successor)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', required=True)
    parser.add_argument('--supplied-only', action='store_true',
                        help='omit diagram recognition probes (small supplied queries still complete)')
    args = parser.parse_args()
    output = dict(passed=False, regina=regina.versionString(), python=sys.version,
        platform=platform.platform(), source_sha256=source_hashes(),
        scope='finite original-standard vertex oracle comparisons and diagram-bound certificate replay; no timing or asymptotic claim',
        models=MODELS, strategies=STRATEGIES, diagram_config=DIAGRAM_CONFIG,
        standard_vertex_oracles={}, supplied=[], diagrams=[])
    target = Path(args.output)

    def save():
        target.write_text(json.dumps(json_safe(output), indent=2)+'\n')

    save()
    for case in supplied_cases():
        key = digest(case['source'])
        if key not in output['standard_vertex_oracles']:
            output['standard_vertex_oracles'][key] = standard_oracle(case['source'])
        record = supplied_record(case, output['standard_vertex_oracles'][key])
        output['supplied'].append(record)
        if len(output['supplied']) % 8 == 0:
            save()
            print('supplied', len(output['supplied']), record['id'], flush=True)
    save()
    if not args.supplied_only:
        for name, diagram in diagram_cases():
            print('diagram_start', name, flush=True)
            record = diagram_record(name, diagram)
            output['diagrams'].append(record)
            save()
            print('diagram', name, record['result']['status'], record['result']['stats'], flush=True)
    counts = Counter()
    for record in output['supplied']:
        counts['supplied_positive' if record['oracle_positive'] else 'supplied_negative'] += 1
        for model in MODELS:
            for strategy in STRATEGIES:
                answer = record['results'][model][strategy]
                counts['positive_queries' if record['oracle_positive'] else 'negative_queries'] += 1
                counts['supplied_labelled_quotient_equal'] += 'crushing' in answer
                counts['negative_tree_replays'] += answer.get('independent_tree_replay', False)
    for record in output['diagrams']:
        counts['diagram_'+record['result']['status']] += 1
        counts['diagram_labelled_quotient_equal'] += len(record['labelled_quotient_comparisons'])
    counts['oracle_sources'] = len(output['standard_vertex_oracles'])
    counts['original_standard_vertices'] = sum(oracle['standard_vertex_count']
        for oracle in output['standard_vertex_oracles'].values())
    output['summary'] = dict(counts)
    assert output['source_sha256'] == source_hashes(), 'audited source changed during run'
    output['passed'] = True
    save()
    print('summary', dict(counts), flush=True)


if __name__ == '__main__':
    main()
