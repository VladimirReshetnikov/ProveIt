"""Optional independent legal-move and replacement checks against Regina."""
import argparse
import json
from pathlib import Path

from fastunknot.pachner_commitments import _State, _Names, _events, _advance
from fastunknot.normal_surface_geometry import _EDGES
from normal_orbit_research.fixtures import regina_triangulation


def main():
    import regina
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--input', required=True)
    parser.add_argument('--output', required=True)
    args = parser.parse_args()
    data = json.loads(Path(args.input).read_text())
    seen, rows, replacements = set(), [], 0
    for case in data['cases']:
        proofs = [proof for run in case['runs'].values() for proof in run['endpoints']]
        for proof in proofs:
            trace = proof['moves']
            raw = trace[-1]['triangulation'] if trace else case['triangulation']
            h = trace[-1]['transport']['heights'] if trace else case['heights']
            encoded = json.dumps([raw, h], sort_keys=True)
            if encoded in seen:
                continue
            seen.add(encoded)
            tri = regina_triangulation(raw)
            n = len(raw['tetrahedra'])
            state = _State(raw, h, tuple(range(n)), 0, 0, ())
            names = _Names(n)
            native = _events(state, True, lambda: None)
            oracle = {}
            for edge in tri.edges():
                if tri.hasPachner(edge):
                    ports = []
                    for emb in edge.embeddings():
                        a, b = sorted((emb.vertices()[0], emb.vertices()[1]))
                        ports.append((emb.tetrahedron().index(), _EDGES.index((a, b))))
                    oracle[('down', tuple(sorted(ports)))] = ('down', edge.index())
            for face in tri.triangles():
                if tri.hasPachner(face):
                    ports = [(emb.tetrahedron().index(), emb.vertices()[3])
                             for emb in face.embeddings()]
                    oracle[('up', tuple(sorted(ports)))] = ('up', face.index())
            if {event.key for event in native} != set(oracle):
                raise AssertionError(('legal move discrepancy', case['name'], n,
                                      {event.key for event in native} ^ set(oracle)))
            for event in native:
                produced = _advance(state, event, names, lambda: None)
                kind, index = oracle[event.key]
                independently_moved = regina.Triangulation3(tri)
                face = (independently_moved.edge(index) if kind == 'down'
                        else independently_moved.triangle(index))
                if not independently_moved.pachner(face):
                    raise AssertionError('Regina rejected its eligible move')
                if independently_moved.isoSig() != regina_triangulation(produced.raw).isoSig():
                    raise AssertionError('independent replacement discrepancy')
                replacements += 1
            rows.append(dict(source_case=case['name'], tetrahedra=n,
                             legal_downward=sum(e.kind == 'down' for e in native),
                             legal_upward=sum(e.kind == 'up' for e in native)))
    result = dict(regina_version=regina.versionString(), source_states=len(rows),
                  checked_replacements=replacements, mismatch_count=0, rows=rows)
    Path(args.output).write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps({key: value for key, value in result.items() if key != 'rows'}))


if __name__ == '__main__':
    main()
