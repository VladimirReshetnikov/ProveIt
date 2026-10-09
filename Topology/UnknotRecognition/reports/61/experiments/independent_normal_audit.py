#!/usr/bin/env python3
"""Independent literal-graph and Regina audit of normal component profiles.

Run with the project's fast/ directory on PYTHONPATH, or pass --fast-root.
The only optional runtime dependency is Regina, required by this audit.
No coordinate magnitude or connected-component multiplicity is expanded by
the production code.  The deliberately literal oracle only uses these small
test inputs, so it provides a separate implementation for comparison.

The trefoil fixture stores the exact five-tetrahedron finite triangulation
and fifteen normal coordinate vectors used in the original audit.  It is
loaded directly, without calling simplify() or enumerating trefoil surfaces.
"""

from argparse import ArgumentParser
from collections import Counter
from hashlib import sha256
from itertools import product
import json
from pathlib import Path
import sys
from time import perf_counter


FIELDS = (
    'euler_characteristic', 'normal_disks', 'boundary_vertices',
    'cycle_0_intersections', 'cycle_1_intersections',
)


def digest(value):
    encoded = json.dumps(value, sort_keys=True, separators=(',', ':')).encode()
    return sha256(encoded).hexdigest()


def main():
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--fast-root', type=Path,
                        help='directory containing fastunknot and normal_orbit_research')
    parser.add_argument('--output', type=Path,
                        default=Path(__file__).with_suffix('.json'))
    parser.add_argument('--trefoil-fixture', type=Path,
                        default=Path(__file__).with_name('finite_trefoil_fixture.json'))
    args = parser.parse_args()
    if args.fast_root is not None:
        sys.path.insert(0, str(args.fast_root.resolve()))

    import regina
    from fastunknot.normal_component_profile import (
        component_weight_system, normal_component_profile,
    )
    from fastunknot.normal_surface_geometry import (
        _prepare, _coordinates, _EDGES, _edge,
    )
    from normal_orbit_research.fixtures import (
        layered_torus, boundary_cap, interior_vertex_torus,
        regina_triangulation, regina_surface, export_surface,
    )

    started = perf_counter()
    records = []

    def literal_profile(raw, vector):
        prepared = _prepare(raw, lambda: None)
        analysed = _coordinates(prepared, vector, lambda: None)
        size, pairs, runs, cycles = component_weight_system(prepared, analysed)
        parents = list(range(size))

        def find(x):
            while parents[x] != x:
                parents[x] = parents[parents[x]]
                x = parents[x]
            return x

        for pairing in pairs:
            for x in range(pairing.a, pairing.b + 1):
                parents[find(x)] = find(pairing.image(x))
        weights = {}
        for start, stop, value in runs:
            for x in range(start, stop):
                destination = weights.setdefault(find(x), [0] * len(FIELDS))
                for j, entry in enumerate(value):
                    destination[j] += entry
        profile = Counter(tuple(value) for value in weights.values())
        return prepared, profile, cycles, size

    def compare(name, family, raw, vector):
        prepared, literal, cycles, size = literal_profile(raw, vector)
        native_triangulation = regina_triangulation(raw)
        edge_map = {}
        for tetrahedron in range(len(vector)):
            for local_index, (a, b) in enumerate(_EDGES):
                root = prepared['edge_roots'][_edge(tetrahedron, a, b)]
                edge_map[root] = native_triangulation.tetrahedron(
                    tetrahedron).edge(local_index).index()
        expected = Counter()
        disks = compressing = 0
        components = regina_surface(native_triangulation, vector).components()
        for component in components:
            edge_weights = {edge: int(str(component.edgeWeight(index)))
                            for edge, index in edge_map.items()}
            value = (
                int(str(component.eulerChar())),
                sum(map(sum, export_surface(component))),
                sum(edge_weights[edge] for edge in prepared['boundary_incidence']),
                sum(edge_weights[edge] for edge in cycles[0]),
                sum(edge_weights[edge] for edge in cycles[1]),
            )
            expected[value] += 1
            disks += bool(component.isOrientable() and value[0] == 1
                          and component.countBoundaries() == 1)
            compressing += component.isCompressingDisc()
        if literal != expected:
            raise AssertionError((name, 'literal profile mismatch', literal, expected))

        actual = normal_component_profile(raw, vector)
        compressed = Counter()
        for group in actual['groups']:
            compressed[tuple(group[field] for field in FIELDS)] += group['multiplicity']
        if compressed != expected:
            raise AssertionError((name, 'compressed profile mismatch', compressed, expected))
        observed = (actual['components'], actual['disk_components'],
                    actual['compressing_disk_components'])
        target = (len(components), disks, compressing)
        if observed != target:
            raise AssertionError((name, 'component classification mismatch', observed, target))
        records.append({
            'name': name,
            'family': family,
            'tetrahedra': len(vector),
            'input_sha256': digest({'triangulation': raw, 'coordinates': vector}),
            'literal_points': size,
            'components': len(components),
            'disk_components': disks,
            'compressing_disk_components': compressing,
            'expected_profiles': [[count, list(value)]
                                  for value, count in sorted(expected.items())],
            'passed': True,
        })

    for tetrahedra in range(1, 7):
        raw, meridian = layered_torus(tetrahedra)
        for scale in (0, 1, 2, 3):
            vector = [[scale * value for value in row] for row in meridian]
            compare(f'layered-{tetrahedra}-scale-{scale}', 'layered_meridians', raw, vector)

    raw, meridian = layered_torus(1)
    cap_counts = []
    for caps in range(4):
        triangulation = regina_triangulation(raw)
        vectors = [export_surface(surface) for surface in regina.NormalSurfaces(
            triangulation, regina.NormalCoords.Standard)]
        cap_counts.append(len(vectors))
        for index, vector in enumerate(vectors):
            compare(f'caps-{caps}-surface-{index}', 'boundary_cap_vertex_surfaces',
                    raw, vector)
        raw, meridian = boundary_cap(raw, meridian)

    raw, basis = interior_vertex_torus()
    for sphere, disk, mobius in product(range(4), repeat=3):
        vector = [[sphere * x + disk * y + mobius * z for x, y, z in zip(u, v, w)]
                  for u, v, w in zip(basis['sphere'], basis['boundary_disk'],
                                     basis['mobius'])]
        compare(f'interior-sphere-{sphere}-disk-{disk}-mobius-{mobius}',
                'interior_vertex_mixtures', raw, vector)

    trefoil = json.loads(args.trefoil_fixture.read_text())
    for index, vector in enumerate(trefoil['normal_coordinates']):
        compare(f'trefoil-surface-{index}', 'finite_trefoil_vertex_surfaces',
                trefoil['triangulation'], vector)

    result = {
        'schema': 'independent-normal-component-audit-v1',
        'passed': True,
        'cases': len(records),
        'family_counts': dict(sorted(Counter(row['family'] for row in records).items())),
        'boundary_cap_vertex_surface_counts': cap_counts,
        'weight_fields': list(FIELDS),
        'method': [
            'literal union-find on the original normal-arc point graph',
            'scalar cellular weights summed separately over literal components',
            'production compressed weighted component profile',
            'Regina connected normal-surface components, cellular counts and disk predicates',
        ],
        'regina_version': regina.versionString(),
        'python_version': sys.version.split()[0],
        'script_sha256': sha256(Path(__file__).read_bytes()).hexdigest(),
        'trefoil_fixture_sha256': sha256(args.trefoil_fixture.read_bytes()).hexdigest(),
        'elapsed_seconds': perf_counter() - started,
        'records': records,
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({key: result[key] for key in
                      ('passed', 'cases', 'family_counts', 'regina_version', 'elapsed_seconds')},
                     sort_keys=True))


if __name__ == '__main__':
    main()
