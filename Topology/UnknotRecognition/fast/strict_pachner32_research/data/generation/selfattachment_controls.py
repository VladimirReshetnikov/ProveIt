"""Retain exact tiny 3--2 selfattachment controls; optional fresh Regina check."""
from argparse import ArgumentParser
from copy import deepcopy
from hashlib import sha256
import json
from pathlib import Path
import sys
from unittest.mock import patch

ROOT = Path('/home/codex/.codex/worktrees/cc5b/Proofs/Topology/UnknotRecognition')
sys.path.insert(0, str(ROOT/'fast'))
from fastunknot.normal_pachner32_verify import verify_normal_pachner32
from fastunknot.normal_surface_geometry import _prepare, NormalOrbitError
from fastunknot.pachner23_verify import verify_pachner_23
from fastunknot.pachner32_verify import verify_pachner_32
from normal_orbit_research.fixtures import layered_torus
from tests.test_normal_pachner32_verify import selfattached_fixture


def digest(value):
    return sha256(json.dumps(value, sort_keys=True, separators=(',', ':')).encode()).hexdigest()


def geometry(source):
    p = _prepare(source, lambda: None)
    return dict(tetrahedra=len(p['tetrahedra']), vertices=p['vertices'], edges=p['edges'],
                boundary_faces=p['boundary_faces'],
                native_valid_finite_connected_orientable_torus_boundary=True)


def boundary(source, certificate):
    labels = {r['tetrahedron']: r['vertices'] for r in certificate['region']}
    incidences = {}
    for t, row in labels.items():
        for f in range(4):
            key = tuple(sorted(row[v] for v in range(4) if v != f))
            incidences.setdefault(key, []).append((t, f))
    facets = {where[0] for where in incidences.values() if len(where) == 1}
    assert len(facets) == 6
    entries, pairs, unpaired = [], set(), 0
    for t, f in sorted(facets):
        r = source['tetrahedra'][t][f]
        entry = dict(local_face=[t, f], formal_triangle=sorted(labels[t][v] for v in range(4) if v != f))
        if r is None:
            entry['kind'] = 'ambient_boundary'
            unpaired += 1
        else:
            u, p = r['tetrahedron'], r['permutation']
            target = (u, p[f])
            assert target in facets
            pairs.add(tuple(sorted(((t, f), target))))
            entry.update(kind='region_boundary_selfattachment', target_face=list(target),
                         formal_vertex_map=sorted([labels[t][v], labels[u][p[v]]] for v in range(4) if v != f))
        entries.append(entry)
    assert len(pairs) == 2 and unpaired == 2
    return dict(formal_boundary_facets=6, ambient_boundary_facets=unpaired,
                formal_boundary_selfattachment_pairs=len(pairs), pairs=sorted(pairs),
                survivor_tetrahedra=0, facets=entries)


def regina_control(source, packet, initial):
    import regina
    def convert(raw):
        tri = regina.Triangulation3()
        tets = tri.newTetrahedra(len(raw['tetrahedra']))
        for t, row in enumerate(raw['tetrahedra']):
            for f, r in enumerate(row):
                if r is not None and tets[t].adjacentTetrahedron(f) is None:
                    tets[t].join(f, tets[r['tetrahedron']], regina.Perm4(*r['permutation']))
        return tri
    def summary(tri):
        assert tri.isValid() and tri.isOrientable() and tri.countComponents() == 1
        assert tri.countVertices() == 1 and tri.countBoundaryComponents() == 1
        assert tri.boundaryComponent(0).eulerChar() == 0
        return dict(valid=True, orientable=True, components=1, vertices=1,
                    boundary_components=1, boundary_euler=0, tetrahedra=tri.size(),
                    iso_sig=tri.isoSig())
    a, b = convert(source), convert(packet['successor'])
    before = summary(a)
    edge = a.tetrahedron(0).edge(regina.Edge3.edgeNumber[0][1])
    assert edge.degree() == 3 and not edge.isBoundary()
    assert a.pachner(edge)
    iso = a.isIsomorphicTo(b)
    original_iso = convert(initial).isIsomorphicTo(b)
    assert iso is not None and original_iso is not None
    return dict(version=regina.versionString(), initial=summary(convert(initial)), before=before,
                after=summary(a), native_successor=summary(b), accepted=True,
                labelled_equal=a == b, isomorphic=True,
                isomorphism=[dict(tetrahedron=iso.simpImage(t), vertices=[iso.facetPerm(t)[v] for v in range(4)])
                             for t in range(a.size())], initial_isomorphic_to_successor=True)


def main():
    parser = ArgumentParser()
    parser.add_argument('--regina', action='store_true')
    parser.add_argument('--output', type=Path, default=Path(__file__).with_name('selfattachment-controls.json'))
    args = parser.parse_args()
    source, packet = selfattached_fixture()
    initial = layered_torus(2)[0]
    expansion = dict(schema='pachner-23-v1', tetrahedron=0, face=0)
    assert verify_pachner_23(initial, source, expansion)
    with patch('fastunknot.pachner23.pachner_23', side_effect=AssertionError), \
         patch('fastunknot.pachner32.pachner_32', side_effect=AssertionError):
        assert verify_normal_pachner32(source, packet)
        assert verify_pachner_32(source, packet['successor'], packet['certificate'])
    mutations = []
    def retain(name, before, bad):
        result = verify_normal_pachner32(before, bad)
        assert result is False, name
        mutations.append(dict(id=name, source=before, packet=bad, rejected=True))
    for field, value in [('schema', True), ('schema', 'wrong'), ('source_sha256', '0'*64),
                         ('source_sha256', False), ('successor', None), ('successor', source),
                         ('successor', {'tetrahedra': []}), ('certificate', None), ('extra', 0)]:
        retain('outer-'+field+'-'+str(value)[:12], source, dict(packet, **{field: value}))
    for field in packet:
        bad = deepcopy(packet); del bad[field]
        retain('missing-'+field, source, bad)
    for field, value in [('tetrahedron', True), ('tetrahedron', 0.0), ('tetrahedron', -1),
                         ('tetrahedron', 3), ('vertices', [3, 4, False, 1]),
                         ('vertices', [3, 4, 0.0, 1]), ('vertices', [3, 4, 0, 0]),
                         ('vertices', [4, 3, 0, 1]), ('extra', 0)]:
        bad = deepcopy(packet); bad['certificate']['region'][0][field] = value
        retain('region-'+field+'-'+str(value), source, bad)
    for t, row in enumerate(packet['successor']['tetrahedra']):
        for f, record in enumerate(row):
            if record is not None:
                bad = deepcopy(packet); bad['successor']['tetrahedra'][t][f] = None
                retain('successor-missing-reciprocal-'+str(t)+'-'+str(f), source, bad)
    bad = deepcopy(source); bad['tetrahedra'][0][0]['permutation'][0] = True
    rebound = dict(packet, source_sha256=digest(bad))
    retain('malformed-source-rebound-digest', bad, rebound)
    callback_controls = []
    for stop in (1, 4):
        error, calls = NormalOrbitError('caller interrupt'), [0]
        def cancel():
            calls[0] += 1
            if calls[0] == stop: raise error
        try:
            verify_normal_pachner32(source, packet, check=cancel)
        except NormalOrbitError as observed:
            assert observed is error
        else:
            raise AssertionError('lost caller interruption')
        callback_controls.append(dict(stop=stop, exception_class='NormalOrbitError', identity_preserved=True))
    legacy_error, calls = NormalOrbitError('legacy caller interrupt'), [0]
    def legacy_cancel():
        calls[0] += 1
        if calls[0] == 2: raise legacy_error
    assert verify_pachner_32(source, packet['successor'], packet['certificate'], check=legacy_cancel) is False
    pins = {}
    for path in [ROOT/'fast/fastunknot'/name for name in
                 ('normal_pachner32_verify.py', 'pachner32_verify.py', 'pachner23_verify.py', 'normal_surface_geometry.py')]+[
                 ROOT/'fast/tests/test_normal_pachner32_verify.py', Path(__file__)]:
        pins[str(path)] = sha256(path.read_bytes()).hexdigest()
    output = dict(schema='scratch-pachner32-selfattachments-v1', passed=True,
                  source_sha256=pins, initial=initial, expansion_certificate=expansion,
                  source=source, packet=packet, initial_geometry=geometry(initial),
                  source_geometry=geometry(source), successor_geometry=geometry(packet['successor']),
                  formal_boundary=boundary(source, packet['certificate']),
                  native_expansion_replay=True, native_legacy_replay=True, native_wrapper_replay=True,
                  producers_disabled_during_replay=True, malformed_controls=mutations,
                  malformed_count=len(mutations), callbacks=callback_controls,
                  legacy_callback_gap=dict(stop=2, callback_exception='NormalOrbitError',
                                           returned_false=True, fixed_by_guarded_wrapper=True),
                  source_scope='Conditional supplied solid-torus source; no diagram provenance or knot verdict.',
                  regina=regina_control(source, packet, initial) if args.regina else None)
    args.output.write_text(json.dumps(output, indent=2, sort_keys=True)+'\n')
    print(json.dumps(dict(passed=True, malformed_count=len(mutations), boundary_selfattachment_pairs=2,
                         regina_used=args.regina, output=str(args.output))))


if __name__ == '__main__':
    main()
