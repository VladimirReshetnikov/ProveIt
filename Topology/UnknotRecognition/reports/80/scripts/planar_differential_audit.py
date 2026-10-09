"""Reproduce genuine-sector and abstract-potential planar differential audits.

python planar_differential_audit.py --fast-root PATH --output-dir OUTPUT
"""

import argparse
from collections import Counter
from fractions import Fraction
from hashlib import sha256
from itertools import combinations
import json
from pathlib import Path
import random
import sys
import time
from types import SimpleNamespace


def genuine():
    from fastunknot.normal_sector import sector_rays
    from fastunknot.sector_planar import (
        certify_planar_sector, sector_planar_plan, sector_planar_rays,
    )
    from fastunknot.sector_planar_verify import verify_planar_sector_certificate
    from fastunknot.sector_sparse import PreparedSectorSource
    from normal_orbit_research.fixtures import (
        boundary_cap, interior_vertex_torus, layered_torus,
    )
    rng = random.Random(962034)
    raws = []
    for n in range(1, 5):
        raw, vector = layered_torus(n)
        raws.append(raw)
        for _ in range(3):
            raw, vector = boundary_cap(raw, vector)
            raws.append(raw)
    raws.append(interior_vertex_torus()[0])
    cases, ray_count, skipped = Counter(), 0, 0
    start = time.perf_counter()
    for raw in raws:
        source = PreparedSectorSource(raw)
        for _ in range(100):
            support = [(i, rng.randrange(3)) for i in range(len(raw['tetrahedra']))
                       if rng.random() < 0.65]
            kernel = source.build(support)
            if len(kernel.basis) > 3:
                skipped += 1
                continue
            plan = sector_planar_plan(kernel)
            cases[f'd{len(kernel.basis)}_slice{plan["section_dimension"]}'] += 1
            old = {tuple(x for row in surface for x in row)
                   for surface in sector_rays(kernel, method='arrangement')}
            fresh = list(sector_planar_rays(kernel))
            new = {tuple(x for row in surface for x in row) for surface in fresh}
            assert old == new, (support, len(kernel.basis), old ^ new)
            assert len(new) == len(fresh)
            assert all(kernel.is_standard_ray(surface) for surface in fresh)
            answer = certify_planar_sector(raw, support, source=source)
            assert verify_planar_sector_certificate(raw, answer['certificate'])
            assert answer['rays'] == fresh
            ray_count += len(new)
    return dict(seed=962034, cases=dict(cases), compared=sum(cases.values()),
                skipped_dimension_over_three=skipped, ray_occurrences=ray_count,
                independently_replayed_certificates=sum(cases.values()),
                seconds=time.perf_counter()-start,
                scope='Genuine layered, capped, and interior-vertex solid-torus '
                      'sectors, compared with the previous complete enumerator.')


def abstract():
    from fastunknot.normal_sector import _nullspace, _primitive, _rref
    from fastunknot.sector_planar import sector_planar_plan
    rng = random.Random(821315)
    totals, points_total = Counter(), 0
    start = time.perf_counter()
    for number in range(240):
        dimension = 1+number % 3
        width = dimension+3
        basis = [[int(i == j) for i in range(dimension)]
                 + [rng.randrange(-2, 4) for _ in range(3)]
                 for j in range(dimension)]
        if number % 7 == 0:
            basis = [[int(i == j) for i in range(dimension)]
                     + [-int(i == j) for i in range(dimension)]
                     + [0]*(3-dimension) for j in range(dimension)]
        groups, potentials, roots, cursor = [], {}, [], 0
        for group in range(1+number % 3):
            size = rng.randrange(1, 6)
            indices = tuple(range(cursor, cursor+size))
            groups.append(indices)
            for corner in indices:
                potentials[corner] = tuple(rng.randrange(-3, 4) for _ in range(width))
                roots.append(group)
            cursor += size
        kernel = SimpleNamespace(
            basis=tuple(tuple(map(Fraction, row)) for row in basis),
            groups=tuple(groups), classes=tuple(range(cursor)),
            potentials=potentials, prepared={'vertex_roots': roots})
        plan = sector_planar_plan(kernel)
        observed = set()
        if plan['chart'] is not None:
            for point in plan['points']:
                observed.add(tuple(form[0]+sum(a*x for a, x in zip(form[1:], point))
                                   for form in plan['chart']['forms']))
        normals = [tuple(basis[j][i] for j in range(dimension)) for i in range(width)]
        for group in groups:
            for left, right in combinations(group, 2):
                difference = [x-y for x, y in zip(potentials[left], potentials[right])]
                normals.append(tuple(sum(x*y for x, y in zip(difference, row))
                                     for row in basis))
        normals = sorted({_primitive(row) for row in normals if any(row)})
        expected = set()
        for selected in combinations(normals, dimension-1):
            null = _nullspace(selected, dimension)
            if len(null) != 1:
                continue
            q = _primitive(sum(basis[j][i]*null[0][j] for j in range(dimension))
                           for i in range(width))
            if not any(q) or any(x < 0 for x in q):
                continue
            active = [tuple(basis[j][i] for j in range(dimension))
                      for i, x in enumerate(q) if x == 0]
            for group in groups:
                values = {c: sum(x*y for x, y in zip(potentials[c], q)) for c in group}
                least = min(values.values())
                minima = [c for c in group if values[c] == least]
                for corner in minima[1:]:
                    difference = [x-y for x, y in
                                  zip(potentials[corner], potentials[minima[0]])]
                    active.append(tuple(sum(x*y for x, y in zip(difference, row))
                                        for row in basis))
            if len(_rref(active, dimension)[1]) == dimension-1:
                total = sum(q)
                expected.add(tuple(Fraction(x, total) for x in q))
        assert observed == expected, (number, basis, groups, potentials, observed ^ expected)
        totals[f'd{dimension}_slice{plan["section_dimension"]}'] += 1
        points_total += len(observed)
    return dict(seed=821315, compared=sum(totals.values()), cases=dict(totals),
                points=points_total, seconds=time.perf_counter()-start,
                scope='Abstract potential cones. All equality intersections and '
                      'active-rank conditions are independent of polygon clipping; '
                      'these are not geometric triangulation claims.')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--fast-root', type=Path, required=True)
    parser.add_argument('--output-dir', type=Path, required=True)
    args = parser.parse_args()
    sys.path.insert(0, str(args.fast_root.resolve()))
    args.output_dir.mkdir(parents=True, exist_ok=True)
    names = ['fastunknot/normal_sector.py', 'fastunknot/sector_sparse.py',
             'fastunknot/sector_planar.py', 'fastunknot/sector_planar_verify.py',
             'normal_orbit_research/fixtures.py']
    pins = {name: sha256((args.fast_root/name).read_bytes()).hexdigest() for name in names}
    for label, run in (('genuine', genuine), ('abstract', abstract)):
        result = run()
        assert pins == {name: sha256((args.fast_root/name).read_bytes()).hexdigest()
                        for name in names}, 'source changed while the audit was running'
        result['source_sha256'] = pins
        path = args.output_dir/f'planar_{label}_differential.json'
        path.write_text(json.dumps(result, indent=2)+'\n')
        print(label, result['compared'], round(result['seconds'], 4), flush=True)


if __name__ == '__main__':
    main()
