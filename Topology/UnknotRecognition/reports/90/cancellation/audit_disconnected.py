"""Reproduce the two-component fixture and optionally its external full census."""
import bootstrap
import argparse
import json
import time

from fastunknot.normal_weight_clusters import prepare_clusters, support_components
from fastunknot.normal_surface_geometry import _coordinates
from fastunknot.normal_vertex_gate import (
    produce_vertex_disc_certificate, verify_vertex_disc_certificate,
)
from fastunknot.pachner23 import pachner_23
from fastunknot.pachner23_verify import verify_pachner_23
from normal_orbit_research.fixtures import regina_triangulation, export_surface
from normal_orbit_research.weight_defect import layered_obstruction


def construct():
    raw, _, layers = layered_obstruction(4)
    start = raw
    moves = []
    for site in [(4, 0), (5, 0), (12, 0)]:
        step = pachner_23(raw, *site)
        assert verify_pachner_23(raw, step['triangulation'], step['certificate'])
        moves.append(dict(site=list(site), certificate=step['certificate'],
                          triangulation=step['triangulation']))
        raw = step['triangulation']
    return start, layers, moves, raw


def main(full_census):
    start, layers, moves, raw = construct()
    saved = json.loads((bootstrap.HERE/'artifacts/disconnected_disc.json').read_text())
    assert raw == saved['triangulation']
    context = prepare_clusters(raw)
    assert context.degree == 8
    assert verify_vertex_disc_certificate(raw, saved['coordinates'], saved['certificate'])
    data = _coordinates(context.prepared, saved['coordinates'], lambda: None)
    increments = {e: data['weights'][e]-context.baseline[e] for e in context.edges
                  if data['weights'][e] != context.baseline[e]}
    assert increments == {47: 4, 53: 4}
    assert support_components(context, increments) == ((47,), (53,))
    saved.update(starting_triangulation=start, boundary_layers=layers, moves=moves,
                 baseline_coordinates=[list(row) for row in context.baseline_rows],
                 baseline_euler=context.baseline_euler,
                 baseline_pieces=sum(map(sum, context.baseline_rows)),
                 disc_pieces=sum(map(sum, saved['coordinates'])),
                 edge_degree=context.degree,
                 defect_stars={e: sorted(context.stars[e]) for e in increments})
    if full_census:
        import regina
        tri = regina_triangulation(raw)
        assert tri.isSolidTorus()
        vectors, algorithms = [], []
        for flags in [regina.NS_VERTEX_TREE | regina.NS_VERTEX_STD_DIRECT,
                      regina.NS_VERTEX_DD | regina.NS_VERTEX_STD_DIRECT]:
            started = time.perf_counter()
            surfaces = regina.NormalSurfaces(tri, regina.NS_STANDARD,
                regina.NS_VERTEX | regina.NS_EMBEDDED_ONLY, flags)
            vector_list = sorted(tuple(x for row in export_surface(surface) for x in row)
                                 for surface in surfaces)
            vectors.append(vector_list)
            algorithms.append(dict(requested=str(flags), actual=str(surfaces.algorithm()),
                                   seconds=time.perf_counter()-started,
                                   standard_vertex_count=len(vector_list)))
        assert vectors[0] == vectors[1]
        discs = []
        for flat in vectors[0]:
            rows = [list(flat[7*t:7*t+7]) for t in range(tri.size())]
            data = _coordinates(context.prepared, rows, lambda: None)
            if (data['euler_characteristic'] != 1
                    or not any(data['weights'][e] % 2
                               for e in context.prepared['boundary_incidence'])):
                continue
            proof = produce_vertex_disc_certificate(raw, rows)
            assert proof and verify_vertex_disc_certificate(raw, rows, proof)
            delta = {e: data['weights'][e]-context.baseline[e] for e in context.edges}
            assert all(value >= 0 and value % 2 == 0 for value in delta.values())
            support = tuple(e for e in context.edges if delta[e])
            discs.append(dict(coordinates=rows, certificate=proof,
                increments={e: delta[e] for e in support},
                components=support_components(context, support)))
        discs.sort(key=lambda item: (len(item['increments']), item['coordinates']))
        assert [(len(d['increments']),len(d['components'])) for d in discs] == [(2,2),(4,2),(4,2)]
        saved['all_vertex_meridians'] = discs
        saved['regina_census'] = dict(version=regina.versionString(),
            standard_vertex_count=len(vectors[0]), meridian_count=len(discs),
            algorithms=algorithms, equality=True,
            scope='Independent exact positive certificates for every meridian; '
                  'completeness evidence is external enumeration, not an independent negative certificate.')
        (bootstrap.HERE/'artifacts/disconnected_all_vertices.json').write_text(json.dumps(
            dict(triangulation=raw,standard_vertices=vectors[0]),indent=2)+'\n')
    (bootstrap.HERE/'artifacts/disconnected_disc.json').write_text(json.dumps(saved,indent=2)+'\n')
    print(json.dumps(dict(certified=True, tetrahedra=len(raw['tetrahedra']),
                          increments=increments, components=[[47],[53]], full_census=full_census)))


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--full-census', action='store_true')
    main(parser.parse_args().full_census)
