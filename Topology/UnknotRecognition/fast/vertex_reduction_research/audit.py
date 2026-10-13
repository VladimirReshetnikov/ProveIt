"""Fresh Regina audit of expanded-edge links, extracted rays and labelled chains.

Run from fast/: python -B -m vertex_reduction_research.audit --output PATH
Regina is used only by this research oracle. The source arrays, raw/canonical
vectors, extracted ray, labelled quotient and existing certificates are kept.
"""
import argparse
from collections import Counter
from hashlib import sha256
import json
from pathlib import Path
import platform
import sys
import regina

from fastunknot.diagram_exterior import diagram_exterior
from fastunknot.diagram_exterior_verify import verify_diagram_exterior
from fastunknot.boundary_shellings import shell_boundary
from fastunknot.boundary_shellings_verify import verify_boundary_shellings
from fastunknot.normal_vertex_reduction import vertex_reduction_ray
from fastunknot.normal_crushing import crush_normal_ray
from fastunknot.normal_crushing_verify import verify_normal_crushing
from fastunknot.normal_crushing_chain import verify_crushing_chain
from normal_crushing_research.fixtures import regina_triangulation, coordinates
from normal_crushing_research.oracle import inspect
from .fixtures import supplied_sources, diagram_cases
from .benchmark import source_hashes


def digest(value):
    return sha256(json.dumps(value, sort_keys=True, separators=(',', ':')).encode()).hexdigest()


def component_summary(surface, triangulation):
    return [dict(coordinates=coordinates(component, triangulation),
                 euler=int(str(component.eulerChar())),
                 vertex_link=component.isVertexLinking(),
                 orientable=component.isOrientable(), boundary=component.hasRealBoundary())
            for component in surface.components()]


def canonical_peel(triangulation, rows):
    """Use Regina's vertex identifications, independently of native roots."""
    groups = {}
    for t, tetrahedron in enumerate(triangulation.tetrahedra()):
        for v in range(4):
            groups.setdefault(tetrahedron.vertex(v).index(), []).append((t, v))
    result = [row[:] for row in rows]
    removed = []
    for vertex, corners in sorted(groups.items()):
        amount = min(rows[t][v] for t, v in corners)
        if amount:
            removed.append(dict(vertex=vertex, multiplicity=amount,
                link_euler=int(triangulation.vertex(vertex).linkEulerChar())))
        for t, v in corners:
            result[t][v] -= amount
    return result, removed


def standard_vertices(triangulation):
    surfaces = regina.NormalSurfaces(triangulation, regina.NormalCoords.Standard,
                                    regina.NormalList.Vertex)
    return [dict(coordinates=coordinates(surface, triangulation),
                 euler=int(str(surface.eulerChar())), vertex_link=surface.isVertexLinking())
            for surface in surfaces]


def audit_source(source, *, result=None, enumerate_standard=False):
    triangulation = regina_triangulation(source)
    assert triangulation.isValid() and triangulation.isOrientable()
    assert triangulation.countBoundaryComponents() == 1
    assert triangulation.boundaryComponent(0).eulerChar() == 0
    result = vertex_reduction_ray(source) if result is None else result
    record = dict(source=source, source_sha256=digest(source), native=result,
                  oracle_vertices=triangulation.countVertices())
    assert result['stats']['vertex_count'] == triangulation.countVertices()
    if result['status'] == 'ONE_VERTEX':
        assert triangulation.countVertices() == 1
        assert all(result[key] is None for key in
                   ('raw_coordinates', 'canonical_coordinates', 'coordinates', 'diagnostics', 'extraction_stats'))
        return record
    assert result['status'] == 'POSITIVE_EULER' and triangulation.countVertices() > 1
    diagnostics = result['diagnostics']
    t, a, b = diagnostics['seed_edge_local']
    seed = triangulation.tetrahedron(t).edge(regina.Edge3.edgeNumber[a][b])
    assert seed.vertex(0) != seed.vertex(1)
    boundary_vertices = sum(v.isBoundary() for v in triangulation.vertices())
    assert diagnostics['boundary_vertices'] == boundary_vertices
    if boundary_vertices > 1:
        assert seed.isBoundary()
    else:
        assert seed.vertex(0).isBoundary() != seed.vertex(1).isBoundary()
    raw, thin = seed.linkingSurface()
    raw_rows = coordinates(raw, triangulation)
    assert raw_rows == result['raw_coordinates'], 'native expansion disagrees with Regina edge-link normalisation'
    canonical, peeled = canonical_peel(triangulation, raw_rows)
    assert canonical == result['canonical_coordinates']
    peeled_surface = regina.NormalSurface(triangulation, regina.NormalCoords.Standard,
                                        [x for row in canonical for x in row])
    raw_components = component_summary(raw, triangulation)
    canonical_components = component_summary(peeled_surface, triangulation)
    for component in raw_components+canonical_components:
        assert component['orientable'] and component['euler'] in (1, 2)
        assert component['boundary'] == (component['euler'] == 1)
    assert any(c['euler'] == 1 and not c['vertex_link'] for c in raw_components)
    assert canonical_components and all(not c['vertex_link'] for c in canonical_components)
    assert peeled_surface.eulerChar() > 0 and any(any(row[4:]) for row in canonical)
    assert int(str(raw.eulerChar()))-int(str(peeled_surface.eulerChar())) == sum(
        entry['multiplicity']*entry['link_euler'] for entry in peeled)
    maximum = max(x for row in raw_rows for x in row)
    pieces = sum(sum(row) for row in raw_rows)
    assert maximum <= 2 and pieces <= 4*triangulation.size()
    assert result['stats']['maximum_raw_coordinate'] == maximum
    assert result['stats']['raw_normal_pieces'] == pieces
    assert result['stats']['raw_euler'] == int(str(raw.eulerChar()))
    assert result['stats']['canonical_euler'] == int(str(peeled_surface.eulerChar()))
    assert result['stats']['peeled_vertex_links'] == sum(entry['multiplicity'] for entry in peeled)

    repeated_faces, repeated_seed_faces = [], []
    for tet in triangulation.tetrahedra():
        for f in range(4):
            edges = [tet.edge(regina.Edge3.edgeNumber[u][v]).index()
                     for u in range(4) for v in range(u+1, 4) if f not in (u, v)]
            if len(set(edges)) < 3:
                repeated_faces.append([tet.index(), f])
            if edges.count(seed.index()) >= 2:
                repeated_seed_faces.append([tet.index(), f])
    ray_oracle = inspect(source, result['coordinates'])
    assert ray_oracle['eligible'] and ray_oracle['connected'] and not ray_oracle['vertex_link']
    native_crush = crush_normal_ray(source, result['coordinates'])
    packet = native_crush['certificate']
    assert verify_normal_crushing(source, packet)
    for field, reference in (('triangulation', 'quotient'), ('components', 'components'),
                              ('torus_component', 'torus_component'), ('successor', 'successor')):
        assert packet[field] == ray_oracle[reference], field
    assert packet['successor'] is None or len(packet['successor']['tetrahedra']) < len(source['tetrahedra'])
    record.update(regina=dict(seed_edge=seed.index(), thin=thin, raw_coordinates=raw_rows,
        raw_components=raw_components, canonical_components=canonical_components,
        peeled_vertex_links=peeled, raw_euler=int(str(raw.eulerChar())),
        canonical_euler=int(str(peeled_surface.eulerChar())), raw_normal_pieces=pieces,
        maximum_raw_coordinate=maximum, repeated_face_edge_occurrences=repeated_faces,
        repeated_seed_face_occurrences=repeated_seed_faces, extracted_ray=ray_oracle),
        crushing=native_crush)
    if enumerate_standard:
        vertices = standard_vertices(triangulation)
        matches = [i for i, vertex in enumerate(vertices)
                   if vertex['coordinates'] == result['coordinates']]
        assert len(matches) == 1, 'extracted ray is absent from the fresh original standard vertex list'
        record['standard_vertex_oracle'] = dict(vertices=vertices, extracted_ray_index=matches[0])
    return record


def audit_diagram(name, diagram):
    initial = diagram_exterior(diagram)
    assert verify_diagram_exterior(diagram, initial)
    shell = shell_boundary(initial)
    shelling = {key: shell[key] for key in ('triangulation', 'moves')}
    current = shelling['triangulation']
    assert verify_boundary_shellings(initial, current, shelling['moves'])
    records, steps = [], []
    while current is not None:
        result = vertex_reduction_ray(current)
        if result['status'] == 'ONE_VERTEX':
            assert regina_triangulation(current).countVertices() == 1
            break
        record = audit_source(current, result=result, enumerate_standard=len(current['tetrahedra']) <= 6)
        records.append(record)
        packet = record['crushing']['certificate']
        steps.append(packet)
        current = packet['successor']
    chain = dict(schema='diagram-crushing-v1', input_pd=[list(row) for row in diagram.pd],
        source_triangulation=initial, shelling=shelling, steps=steps,
        status='UNKNOT' if current is None else 'REDUCED', triangulation=current)
    assert verify_crushing_chain(diagram, chain)
    assert len(steps) <= len(shelling['triangulation']['tetrahedra'])
    return dict(id=name, input_pd=[list(row) for row in diagram.pd], records=records, chain=chain,
        independent_chain_replay=True, preprocessing_status='UNKNOT' if current is None else 'ONE_VERTEX',
        initial_tetrahedra=len(initial['tetrahedra']), shelled_tetrahedra=len(shelling['triangulation']['tetrahedra']),
        successor_tetrahedra=0 if current is None else len(current['tetrahedra']),
        successor_vertices=0 if current is None else regina_triangulation(current).countVertices())


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', required=True)
    args = parser.parse_args()
    output = dict(passed=False, regina=regina.versionString(), python=sys.version,
        platform=platform.platform(), source_sha256=source_hashes(),
        scope='fresh labelled edge-link, canonical peeling, original-source extreme-ray and crushing quotient checks; diagram chains authenticate only unknot terminality or a one-vertex exterior',
        supplied=[], diagrams=[])
    target = Path(args.output)

    def save():
        target.write_text(json.dumps(output, indent=2)+'\n')

    for fixture in supplied_sources():
        record = audit_source(fixture['source'], enumerate_standard=fixture['enumerate_standard'])
        record['fixture'] = {key: value for key, value in fixture.items() if key != 'source'}
        output['supplied'].append(record)
        print(fixture['id'], record['native']['status'], record['native']['stats'], flush=True)
    save()
    for name, diagram in diagram_cases():
        record = audit_diagram(name, diagram)
        output['diagrams'].append(record)
        save()
        print(name, record['preprocessing_status'], len(record['records']),
              record['successor_tetrahedra'], flush=True)
    records = output['supplied']+[r for case in output['diagrams'] for r in case['records']]
    counts = Counter()
    for record in records:
        counts[record['native']['status']] += 1
        if record['native']['status'] == 'ONE_VERTEX':
            continue
        raw = record['native']['raw_coordinates']
        counts['regina_edge_link_equal'] += 1
        counts['regina_labelled_quotient_equal'] += 1
        counts['expanded_links'] += bool(record['native']['diagnostics']['face_additions'])
        counts['peeled_links'] += bool(record['regina']['peeled_vertex_links'])
        counts['double_triangle'] += any(2 in row[:4] for row in raw)
        counts['double_quad'] += any(2 in row[4:] for row in raw)
        counts['repeated_seed_face'] += bool(record['regina']['repeated_seed_face_occurrences'])
        counts['fresh_standard_vertex_lists'] += 'standard_vertex_oracle' in record
    assert counts['expanded_links'] and counts['peeled_links'] and counts['double_triangle']
    assert counts['repeated_seed_face'] and counts['fresh_standard_vertex_lists']
    output['summary'] = dict(counts)
    if output['source_sha256'] != source_hashes():
        raise AssertionError('audited source changed during the run')
    output['passed'] = True
    save()
    print('summary', dict(counts), flush=True)


if __name__ == '__main__':
    main()
