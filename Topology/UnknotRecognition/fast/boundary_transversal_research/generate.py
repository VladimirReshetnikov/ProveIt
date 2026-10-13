"""Optional fresh Regina regeneration of the six retained boundary layers."""
import argparse
import json
from pathlib import Path

from fastunknot.normal_surface_geometry import _quad
from .common import digest, load, source_hashes, verify_generation_provenance
from .replay import check_layer, observation


def regina_triangulation(source):
    import regina
    result = regina.Triangulation3()
    tetrahedra = result.newTetrahedra(len(source['tetrahedra']))
    for t, faces in enumerate(source['tetrahedra']):
        for f, record in enumerate(faces):
            if record is not None and tetrahedra[t].adjacentTetrahedron(f) is None:
                tetrahedra[t].join(f, tetrahedra[record['tetrahedron']],
                                   regina.Perm4(*record['permutation']))
    return result


def face_pairing(triangulation):
    return dict(tetrahedra=[[
        None if tet.adjacentTetrahedron(f) is None else
        dict(tetrahedron=tet.adjacentTetrahedron(f).index(),
             permutation=[tet.adjacentGluing(f)[j] for j in range(4)])
        for f in range(4)] for tet in triangulation.tetrahedra()])


def extend(source, rows, chi):
    """Enumerate only the small local extensions in these fixed fixtures."""
    t = len(rows)
    arcs = []
    for f, record in enumerate(source['tetrahedra'][t]):
        if record is None:
            continue
        assert record['tetrahedron'] < t
        old, perm = rows[record['tetrahedron']], record['permutation']
        for v in range(4):
            if v != f:
                arcs.append((f, v, old[perm[v]]+old[4+_quad(perm[v], perm[f])]))
    for value in range(1+max(a for _, _, a in arcs)):
        for typ in range(3):
            triangles = {}
            for f, v, a in arcs:
                x = a-int(typ == _quad(v, f))*value
                if x < 0 or (v in triangles and triangles[v] != x):
                    break
                triangles[v] = x
            else:
                assert len(triangles) == 4
                new = [triangles[v] for v in range(4)]+[value*int(q == typ) for q in range(3)]
                candidate = rows+[new]
                try:
                    obs, _ = observation(source, candidate)
                except AssertionError:
                    continue
                if obs['canonical_euler'] == chi:
                    return candidate, obs
    raise AssertionError('no preserving primitive extreme extension')


def main():
    import regina
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    pins = source_hashes()
    verify_generation_provenance()
    historical = load('provenance/layer-refuter.json')
    records = []
    for retained in historical['records']:
        source, rows = retained['initial_source'], retained['initial_coordinates']
        tri = regina_triangulation(source)
        record = {key: value for key, value in retained.items() if key != 'steps'}
        record['steps'] = []
        for saved in retained['steps']:
            t, e = saved['flipped_original_local_edge']
            edge = tri.tetrahedron(t).edge(e)
            assert edge.isBoundary()
            new = tri.layerOn(edge)
            assert tri.isValid() and tri.isOrientable() and tri.countVertices() == 1
            following = face_pairing(tri)
            rows, obs = extend(following, rows, retained['initial']['canonical_euler'])
            step = dict(flipped_original_local_edge=[t, e], new_tetrahedron=new.index(),
                        source=following, coordinates=rows, observation=obs)
            check_layer(source, step)
            assert step == saved, 'fresh labelled Regina construction differs'
            record['steps'].append(step)
            source = following
        assert digest(source) == record['final_source_sha256']
        records.append(record)
    assert records == historical['records']
    assert source_hashes() == pins, 'source changed during regeneration'
    args.output.write_text(json.dumps(dict(schema='boundary-transversal-regeneration-v1',
        passed=True, source_sha256=pins, regina_version=regina.versionString(),
        records=records, matches_retained=True,
        scope='Fresh six-layer construction and local extension search, not fresh root-ray enumeration or a native search benchmark.'), indent=2)+'\n')
    print('PASSED: fresh Regina generation exactly matches all six labelled retained layers.')


if __name__ == '__main__':
    main()
