"""Bounded deterministic fixture search; retained hits get exact certificates."""
import bootstrap
import json
import random
import time
import regina
from fastunknot.normal_weight_clusters import prepare_clusters, support_components
from fastunknot.normal_surface_geometry import _coordinates
from fastunknot.normal_vertex_gate import produce_vertex_disc_certificate, verify_vertex_disc_certificate
from fastunknot.pachner23 import pachner_23
from normal_orbit_research.fixtures import layered_torus, regina_triangulation, export_surface
from normal_orbit_research.weight_defect import layered_obstruction

rng = random.Random(261012191)
started = time.time()
summary = []
for history in range(48):
    if history % 3 == 0:
        raw, _, _ = layered_obstruction(4)
    else:
        raw, _ = layered_torus(5 + history % 4)
    start = raw
    moves = []
    for depth in range(11):
        context = prepare_clusters(raw)
        tri = regina_triangulation(raw)
        if depth >= 3:
            surfaces = regina.NormalSurfaces(tri, regina.NS_STANDARD)
            hits = []
            for surface in surfaces:
                if str(surface.eulerChar()) != '1':
                    continue
                rows = export_surface(surface)
                data = _coordinates(context.prepared, rows, lambda: None)
                if not any(data['weights'][e] % 2
                           for e in context.prepared['boundary_incidence']):
                    continue
                delta = {e: data['weights'][e]-context.baseline[e] for e in context.edges}
                assert all(x >= 0 and x % 2 == 0 for x in delta.values())
                support = tuple(e for e in context.edges if delta[e])
                parts = support_components(context, support)
                hits.append((len(support), len(parts)))
                if len(parts) > 1:
                    proof = produce_vertex_disc_certificate(raw, rows)
                    assert proof is not None
                    assert verify_vertex_disc_certificate(raw, rows, proof)
                    result = dict(history=history, depth=depth, starting_triangulation=start,
                                  moves=moves, triangulation=raw, coordinates=rows,
                                  certificate=proof, baseline=dict(context.baseline),
                                  increments={e: delta[e] for e in support},
                                  components=parts, signature=tri.isoSig(),
                                  elapsed=time.time()-started)
                    (bootstrap.HERE/'artifacts/disconnected_first_search_hit.json').write_text(
                        json.dumps(result, indent=2)+'\n')
                    print('FOUND', history, depth, tri.size(), support, parts,
                          'seconds', time.time()-started, flush=True)
                    raise SystemExit
            summary.append(dict(history=history, depth=depth, tetrahedra=tri.size(),
                                surfaces=surfaces.size(), discs=hits))
            print(history, depth, tri.size(), surfaces.size(), hits,
                  'seconds', round(time.time()-started, 2), flush=True)
        sites = [(t, f) for t, row in enumerate(raw['tetrahedra'])
                 for f, record in enumerate(row)
                 if record is not None and record['tetrahedron'] != t]
        site = rng.choice(sites)
        move = pachner_23(raw, *site)
        moves.append(dict(site=site, certificate=move['certificate']))
        raw = move['triangulation']
(bootstrap.HERE/'artifacts/disconnected_search.json').write_text(json.dumps(summary, indent=2)+'\n')
