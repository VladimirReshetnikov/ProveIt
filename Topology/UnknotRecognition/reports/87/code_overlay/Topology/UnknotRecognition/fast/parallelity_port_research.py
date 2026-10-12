"""Finite topological oracle and reproducible audit for cyclic product ports."""

from collections import defaultdict
from contextlib import ExitStack
from hashlib import sha256
import json
from pathlib import Path
import random
from statistics import median
from time import perf_counter
from unittest.mock import patch


def literal_port_words(geometry, profiles, *, max_points=200000):
    """Walk the actual boundary 1-manifold; no weighted/query helper is used.

    Polygon corners are explicitly glued, every boundary edge is materialized,
    and cyclic order is found by following the two incident boundary darts.
    Fibre gauges are computed separately by ordinary graph propagation.
    """
    size = geometry['polygon_points']
    corner_size = geometry['corner_points']
    if size + corner_size > max_points:
        raise ValueError('literal port oracle exceeds its expansion cap')
    parent = list(range(corner_size))
    graph = defaultdict(list)

    def find(point):
        while parent[point] != point:
            parent[point] = parent[parent[point]]
            point = parent[point]
        return point

    polygons = geometry['polygons']
    for gluing in geometry['gluings']:
        left, right = polygons[gluing['left']], polygons[gluing['right']]
        for rank in range(gluing['rank_start'], gluing['rank_stop']):
            a = gluing['left_map'][0] * rank + gluing['left_map'][1]
            b = gluing['right_map'][0] * rank + gluing['right_map'][1]
            graph[a].append((b, int(gluing['fibre_flip'])))
            graph[b].append((a, int(gluing['fibre_flip'])))
            for end in (0, 1):
                i = (gluing['left_edge'] + end) % len(left['corner_starts'])
                j = (gluing['right_edge'] + (end ^ gluing['ends_reverse']))
                j %= len(right['corner_starts'])
                x = left['corner_starts'][i] + a - left['start']
                y = right['corner_starts'][j] + b - right['start']
                parent[find(x)] = find(y)
    incidence, edges, ports, port_polygons = defaultdict(list), [], {}, {}
    for record in geometry['free_edges']:
        polygon = polygons[record['polygon']]
        corners = polygon['corner_starts']
        for rank in range(record['rank_start'], record['rank_stop']):
            a = find(corners[record['edge']] + rank - 1)
            b = find(corners[(record['edge'] + 1) % len(corners)] + rank - 1)
            number = len(edges)
            label = None if record['original_boundary'] else record['port']
            edges.append((a, b, label))
            incidence[a].append((number, 0))
            incidence[b].append((number, 1))
            if label is not None:
                assert label not in ports
                ports[label] = number
                port_polygons[label] = polygon['start'] + rank - 1
    assert all(len(darts) == 2 for darts in incidence.values())
    visited, words = set(), []
    for port in sorted(ports):
        if port in visited:
            continue
        start = (ports[port], 0)
        current, word = start, []
        while True:
            edge, entry = current
            label = edges[edge][2]
            assert label not in visited
            visited.add(label)
            length = 0
            while True:
                endpoint = edges[edge][1 - entry]
                incoming = (edge, 1 - entry)
                candidates = [dart for dart in incidence[endpoint] if dart != incoming]
                assert len(candidates) == 1
                edge, entry = candidates[0]
                if edges[edge][2] is not None:
                    break
                length += 1
            word.append(dict(port=label, entry_endpoint=current[1],
                             original_edges_after=length))
            current = edge, entry
            if current == start:
                break
        words.append(word)
    colours, components, twisted = {}, {}, set()
    for start in range(size):
        if start in colours:
            continue
        pending = [start]
        colours[start] = 0
        components[start] = start
        for point in pending:
            for neighbour, flip in graph[point]:
                expected = colours[point] ^ flip
                if neighbour not in colours:
                    colours[neighbour] = expected
                    components[neighbour] = start
                    pending.append(neighbour)
                elif colours[neighbour] != expected:
                    twisted.add(start)
    gauges = []
    for profile in profiles:
        labels = profile['core_ports']
        if not labels:
            continue
        anchor = min(labels)
        point = port_polygons[anchor]
        component = components[point]
        assert all(components[port_polygons[label]] == component for label in labels)
        product = component not in twisted
        assert product == profile['product']
        bits = [[label, colours[port_polygons[label]] ^ colours[point]] for label in labels]
        gauges.append(dict(core_ports=labels, product=product, anchor_port=anchor,
                           gauges=bits if product else None))
    return dict(boundary_words=words, fibre_gauges=gauges,
                expanded_polygons=size, expanded_corners=corner_size,
                expanded_boundary_edges=len(edges))


def _disabled_producer_replay(raw, rows, certificate):
    from fastunknot.parallelity_port_words_verify import verify_parallelity_port_words
    disabled = ('fastunknot.normal_parallelity.normal_cut_parallelity',
                'fastunknot.normal_parallelity._parallelity_geometry',
                'fastunknot.normal_parallelity._systems',
                'fastunknot.parallelity_port_words.normal_parallelity_port_words',
                'fastunknot.parallelity_port_words._port_queries',
                'fastunknot.parallelity_port_words._boundary_words',
                'fastunknot.parallelity_port_words._fibre_gauges',
                'fastunknot.parallelity_port_words._disc_templates',
                'fastunknot.interval_orbits.count_orbits')
    with ExitStack() as stack:
        for name in disabled:
            stack.enter_context(patch(name, side_effect=AssertionError('producer used')))
        assert verify_parallelity_port_words(raw, rows, certificate)


def _wire(value):
    from fastunknot.integer_codec import json_safe
    return json.dumps(json_safe(value), sort_keys=True, separators=(',', ':')).encode()


def validate_product_templates(templates):
    """Authenticate actual emitted triangulations with Regina ball recognition.

    This is a research audit, not a dependency of the production or replay
    operators.  The relative topological theorem is their correctness basis.
    """
    from fractions import Fraction
    import regina
    by_size, checked_charts = {}, 0
    for template in templates:
        cells = template['product_tetrahedra']
        sides = template['boundary_sides']
        charts = defaultdict(list)
        for side in sides:
            if side['kind'] != 'core_port':
                continue
            a, b, denominator = side['parameter']
            assert denominator > 0 and 0 <= a < b <= denominator
            charts[side['port']].append((Fraction(a, denominator),
                                         Fraction(b, denominator)))
        assert sorted(charts) == sorted(template['core_ports'])
        for intervals in charts.values():
            intervals.sort()
            assert intervals[0][0] == 0 and intervals[-1][1] == 1
            assert all(a[1] == b[0] for a, b in zip(intervals, intervals[1:]))
            checked_charts += 1
        signature = tuple(tuple(tetrahedron) for tetrahedron in cells)
        if signature in by_size:
            continue
        triangulation = regina.Triangulation3()
        tetrahedra = [triangulation.newTetrahedron() for _ in cells]
        faces = {}
        for index, cell in enumerate(cells):
            assert len(set(cell)) == 4
            for opposite in range(4):
                face = tuple(sorted(cell[j] for j in range(4) if j != opposite))
                if face not in faces:
                    faces[face] = (index, opposite)
                else:
                    other, target = faces.pop(face)
                    image = [None] * 4
                    image[opposite] = target
                    for vertex in range(4):
                        if vertex != opposite:
                            image[vertex] = cells[other].index(cell[vertex])
                    tetrahedra[index].join(opposite, tetrahedra[other], regina.Perm4(*image))
        assert triangulation.isValid()
        assert triangulation.isConnected()
        assert triangulation.isOrientable()
        assert triangulation.countBoundaryComponents() == 1
        assert triangulation.isBall()
        by_size[signature] = dict(tetrahedra=len(cells), base_boundary_vertices=len(sides),
                                  valid=True, connected=True, orientable=True, is_ball=True,
                                  iso_signature=triangulation.isoSig())
    return dict(regina_version=regina.versionString(), templates_checked=len(templates),
                port_charts_checked=checked_charts, distinct_complexes=len(by_size),
                complexes=list(by_size.values()))


def audit(output, *, benchmark_rounds=7):
    from fastunknot.integer_codec import encoded_integer
    from fastunknot.parallelity_port_words import normal_parallelity_port_words
    from fastunknot.parallelity_port_words_verify import _independent_templates
    from fastunknot.normal_parallelity import normal_cut_parallelity
    from fastunknot.normal_parallelity_verify import verify_normal_cut_parallelity
    from normal_orbit_research.fixtures import layered_torus
    from tests.test_normal_surface_orbits import relabel
    root = Path(__file__).resolve().parents[1]
    bank = json.loads((root / 'synthesis/data/parallelity-audit.json').read_text())
    cases = [(r['id'], r['triangulation'], r['coordinates']) for r in bank['source_proofs']]
    rng = random.Random(26101231)
    for t in (1, 2, 4):
        raw, base = layered_torus(t)
        for multiplier in (0, 1, 2, 5):
            cases.append((f'analytic/{t}/{multiplier}', raw,
                          [[multiplier * x for x in row] for row in base]))
        for index in range(6):
            changed, rows = relabel(raw, [[3 * x for x in row] for row in base], rng)
            cases.append((f'relabel/{t}/{index}', changed, rows))
    raw, base = layered_torus(2)
    cases.append(('binary_attached/2/16384', raw,
                  [[(1 << 16384) * x for x in row] for row in base]))
    records, proofs, expanded, templates = [], [], 0, []
    began = perf_counter()
    seen_profiles = set()
    for name, raw, rows in cases:
        native = normal_parallelity_port_words(raw, rows, record_certificate=True)
        assert native['status'] == 'COMPLETE'
        proof = json.loads(_wire(native['certificate']))
        _disabled_producer_replay(raw, rows, proof)
        geometry = native['geometry']
        finite = geometry['polygon_points'] + geometry['corner_points'] <= 300000
        if finite:
            literal = literal_port_words(geometry, native['summary']['base_profiles'],
                                         max_points=300000)
            assert native['boundary_words'] == literal['boundary_words'], name
            assert native['fibre_gauges'] == literal['fibre_gauges'], name
            expanded += literal['expanded_boundary_edges']
        q = len(geometry['ports'])
        tetrahedra = sum(len(t['product_tetrahedra']) for t in native['disc_templates'])
        templates.extend(native['disc_templates'])
        assert tetrahedra <= 9 * q
        record = dict(id=name, tetrahedra=len(rows), core_ports=q,
                      boundary_words=len(native['boundary_words']),
                      attached_disc_products=len(native['disc_templates']),
                      replacement_tetrahedra=tetrahedra, finite_reference=finite,
                      zero_gaps=sum(r['original_edges_after'] == 0
                                    for word in native['boundary_words'] for r in word),
                      positive_gaps=sum(r['original_edges_after'] > 0
                                        for word in native['boundary_words'] for r in word),
                      reversed_port_traversals=sum(r['entry_endpoint'] == 1
                                                  for word in native['boundary_words'] for r in word),
                      nonzero_product_gauges=sum(bit == 1 for group in native['fibre_gauges']
                                                if group['product'] for _, bit in group['gauges']),
                      twisted_port_components=sum(not group['product']
                                                   for group in native['fibre_gauges']),
                      proof_sha256=sha256(_wire(proof)).hexdigest(),
                      largest_input_bits=max((abs(encoded_integer(x)).bit_length()
                                              for row in rows for x in row), default=0))
        records.append(record)
        profile = (q, len(native['disc_templates']),
                   any(r['original_edges_after'] == 0
                       for word in native['boundary_words'] for r in word),
                   any(not g['product'] for g in native['fibre_gauges']))
        if profile not in seen_profiles or not finite:
            seen_profiles.add(profile)
            proofs.append(dict(id=name, triangulation=raw, coordinates=rows, certificate=proof))
    validation = validate_product_templates(templates)
    # Both timing arms construct and replay the same source certificate.
    # The compressed arm also replays its two additional interval proofs;
    # the finite arm follows all literal boundary darts and fibre graph edges.
    timing = []
    for t, multiplier in ((2, 4), (2, 64), (2, 1024), (2, 4096), (4, 64)):
        raw, base = layered_torus(t)
        rows = [[multiplier * x for x in row] for row in base]

        def compressed():
            from fastunknot.parallelity_port_words_verify import verify_parallelity_port_words
            result = normal_parallelity_port_words(raw, rows, record_certificate=True)
            assert verify_parallelity_port_words(raw, rows, result['certificate'])
            return _wire(dict(boundary_words=result['boundary_words'],
                              fibre_gauges=result['fibre_gauges'],
                              disc_templates=result['disc_templates']))

        def literal():
            result = normal_cut_parallelity(raw, rows, record_certificate=True)
            assert verify_normal_cut_parallelity(raw, rows, result['certificate'])
            reference = literal_port_words(result['geometry'], result['summary']['base_profiles'],
                                           max_points=2000000)
            templates = _independent_templates(reference['boundary_words'], reference['fibre_gauges'],
                                               result['summary']['base_profiles'], lambda: None)
            return _wire(dict(boundary_words=reference['boundary_words'],
                              fibre_gauges=reference['fibre_gauges'], disc_templates=templates))

        common_output = compressed()
        assert common_output == literal()
        pairs = []
        for _ in range(benchmark_rounds):
            functions = [('compressed', compressed), ('literal', literal)]
            rng.shuffle(functions)
            times = {}
            for label, function in functions:
                start = perf_counter()
                function()
                times[label] = perf_counter() - start
            times['order'] = [name for name, _ in functions]
            pairs.append(times)
        timing.append(dict(tetrahedra=t, multiplier=multiplier, rounds=pairs,
                           compressed_median_seconds=median(p['compressed'] for p in pairs),
                           literal_median_seconds=median(p['literal'] for p in pairs),
                           common_output_sha256=sha256(common_output).hexdigest(),
                           common_output_bytes=len(common_output),
                           median_literal_over_compressed=median(
                               p['literal'] / p['compressed'] for p in pairs)))
        # Same implementation, same task, same input: this is a timing-noise
        # control, rather than a second algorithmic comparison.
        if t == 2 and multiplier == 64:
            controls = []
            for _ in range(benchmark_rounds):
                labels = ['first', 'second']
                rng.shuffle(labels)
                times = {}
                for label in labels:
                    start = perf_counter()
                    assert compressed() == common_output
                    times[label] = perf_counter() - start
                times['order'] = labels
                controls.append(times)
            control = dict(tetrahedra=t, multiplier=multiplier, rounds=controls,
                           median_second_over_first=median(
                               p['second'] / p['first'] for p in controls))
    pins = {}
    for relative in ('fastunknot/parallelity_port_words.py',
                     'fastunknot/parallelity_port_words_verify.py',
                     'parallelity_port_research.py'):
        pins[relative] = sha256((Path(__file__).parent / relative).read_bytes()).hexdigest()
    report = dict(schema='parallelity-port-audit-v1', finite_cases=sum(r['finite_reference'] for r in records),
                  binary_cases=sum(not r['finite_reference'] for r in records),
                  literal_boundary_edges=expanded, records=records, source_proofs=proofs,
                  template_validation=validation, timing=timing, identical_code_control=control,
                  source_sha256=pins, seconds=perf_counter() - began,
                  benchmark_scope='source construction and replay in both arms; extra weighted replay '
                                  'versus finite boundary walks and fibre propagation; serialization '
                                  'of byte-identical common output in both arms; one warmup per arm, '
                                  'seeded shuffled paired rounds; no knot verdict')
    Path(output).write_bytes(_wire(report) + b'\n')
    print(json.dumps({k: report[k] for k in ('finite_cases', 'binary_cases',
                                          'literal_boundary_edges', 'seconds')}))


if __name__ == '__main__':
    import argparse
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', required=True)
    parser.add_argument('--benchmark-rounds', type=int, default=7)
    arguments = parser.parse_args()
    audit(arguments.output, benchmark_rounds=arguments.benchmark_rounds)
