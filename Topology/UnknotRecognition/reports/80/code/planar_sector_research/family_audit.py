"""Exact, untimed audit of the two-cap Fibonacci source family.

For n base tetrahedra, allow quadrilateral type 2 in the base and type 1
in each of the two caps.  Put A=F_(n+1), B=F_(n+2), and
h=max(0,y-A*x,z-A*x).  The claimed canonical rows are checked against the
native source equations and the complete planar enumerator.  Native
compressed component certificates are independently replayed.  Optional
Regina checks regenerate complete standard vertex lists and classify each
of the seven rays separately.  No timings or performance claims are made.
"""

import argparse
from hashlib import sha256
from itertools import product
import json
from pathlib import Path
import platform

from fastunknot.normal_component_verify import verify_normal_component_certificate
from fastunknot.normal_surface_components import normal_component_census
from fastunknot.sector_planar import (
    certify_planar_sector, sector_planar_plan, sector_planar_rays)
from fastunknot.sector_planar_verify import verify_planar_sector_certificate
from fastunknot.sector_sparse import PreparedSectorSource

from .audit import geometry_metrics, occupied
from .fixtures import double_capped_fibonacci, fresh_standard, ray_digest, to_regina, vector_key


def fibonacci_through(index):
    values = [0, 1]
    while len(values) <= index:
        values.append(values[-1] + values[-2])
    return values


def formula_rows(n, x, y, z):
    if type(n) is not int or n < 1:
        raise ValueError('n must be positive')
    if any(type(value) is not int or value < 0 for value in (x, y, z)):
        raise ValueError('parameters must be nonnegative integers')
    fib = fibonacci_through(n + 2)
    a, b = fib[n + 1], fib[n + 2]
    h = max(0, y - a*x, z - a*x)
    rows = [[fib[n-i+1]*x+h, fib[n-i+1]*x+h, h, h,
             0, 0, fib[n-i]*x] for i in range(n)]
    rows.append([a*x+h-y, b*x+h, 0, h, 0, y, 0])
    rows.append([b*x+h, a*x+h-z, h, 0, 0, z, 0])
    return rows


def parameter_rays(n):
    a = fibonacci_through(n + 1)[n + 1]
    return ((1, 0, 0), (1, a, 0), (1, 0, a), (1, a, a),
            (0, 1, 0), (0, 0, 1), (0, 1, 1))


def _coordinates_in_sector(rows, support):
    return tuple(rows[t][4 + q] for t, q in support)


def _native_classification(raw, rows, x, h):
    census = normal_component_census(raw, rows, mode='summary', record_certificate=True)
    if census['status'] != 'COMPLETE':
        raise AssertionError('uncapped native component census was inconclusive')
    if (census['components'], census['compressing_disk_components'],
            census['euler_characteristic']) != (x + h, x, x + h):
        raise AssertionError(('component formula failed', x, h, census))
    if any(group['euler_characteristic'] != 1 for group in census['component_histogram']):
        raise AssertionError('family contains a nondisc component')
    if not verify_normal_component_certificate(raw, rows, census['certificate']):
        raise AssertionError('independent native component replay failed')
    return census


def run(sizes, *, fresh_regina=False):
    records, certificates = [], []
    native_queries, regina_queries, formula_cases = 0, 0, 0
    for n in sizes:
        if type(n) is not int or n < 1:
            raise ValueError('all sizes must be positive')
        source = double_capped_fibonacci(n)
        raw, support = source['triangulation'], source['allowed_types']
        prepared = PreparedSectorSource(raw)
        kernel = prepared.build(support)
        stats = dict(kernel.stats)
        rays = list(sector_planar_rays(kernel, stats=stats))
        plan = sector_planar_plan(kernel)
        metrics = geometry_metrics(plan)
        fib = fibonacci_through(n + 2)
        a, b = fib[n + 1], fib[n + 2]
        expected = [formula_rows(n, *parameters) for parameters in parameter_rays(n)]
        if len(kernel.basis) != 3 or len(rays) != 7:
            raise AssertionError(('wrong family dimension or output size', n, stats))
        if {vector_key(row) for row in rays} != {vector_key(row) for row in expected}:
            raise AssertionError(('seven-ray formula differs from planar output', n))
        if (metrics['polygon_vertices'], metrics['nontrivial_active_groups'],
                metrics['active_cells'], metrics['internal_edges'],
                metrics['refined_ray_bound']) != (3, 1, 3, 3, 7):
            raise AssertionError(('family does not attain the one-group bound', n, metrics))
        # Check the full canonical-lift formula on a deterministic parameter
        # grid, including all three regions and their shared boundaries.
        grid = tuple(product((0, 1, 2), (0, 1, a, a+1, 2*a+3),
                             (0, 1, a, a+1, 2*a+3)))
        for x, y, z in grid:
            row = formula_rows(n, x, y, z)
            if kernel.lift(_coordinates_in_sector(row, support)) != row:
                raise AssertionError(('canonical coordinate formula failed', n, x, y, z))
        formula_cases += len(grid)

        active_forms = set()
        all_forms = set()
        for corner in kernel.classes:
            potential = kernel.potentials[corner]
            # Express the native source potential in (x,y,z) and add the
            # shared A*x gauge to compare with the stated base-offset formula.
            form = (sum(potential[i] * fib[n-i] for i in range(n)) + a,
                    potential[n], potential[n+1])
            all_forms.add(form)
        for group in plan['groups']:
            for cell in group['cells']:
                potential = kernel.potentials[cell['corner']]
                active_forms.add((sum(potential[i] * fib[n-i] for i in range(n)) + a,
                                  potential[n], potential[n+1]))
        if active_forms != {(0, 0, 0), (a, -1, 0), (a, 0, -1)}:
            raise AssertionError(('wrong active minimum functions', n, active_forms))

        certified = certify_planar_sector(raw, support, source=prepared)
        if certified['status'] != 'COMPLETE' or not verify_planar_sector_certificate(
                raw, certified['certificate']):
            raise AssertionError(('independent family coverage replay failed', n))
        certificates.append(dict(
            source_id=f'double_cap_fibonacci_{n:03d}', triangulation=raw,
            certificate=certified['certificate'], ray_sha256=ray_digest(rays)))

        regina_tri = None
        regina_source = None
        if fresh_regina:
            import regina
            regina_tri = to_regina(raw)
            regina_source = dict(
                valid=regina_tri.isValid(), orientable=regina_tri.isOrientable(),
                connected=regina_tri.isConnected(), solid_torus=regina_tri.isSolidTorus(),
                vertices=regina_tri.countVertices(),
                boundary_components=regina_tri.countBoundaryComponents(),
                isosig=regina_tri.isoSig())
            if not (regina_source['valid'] and regina_source['orientable'] and
                    regina_source['connected'] and regina_source['solid_torus']):
                raise AssertionError(('Regina rejected claimed source topology', n, regina_source))
            full = fresh_standard(raw)
            allowed = set(support)
            restricted = [row for row in full if set(occupied(row)) and
                          set(occupied(row)) <= allowed]
            if {vector_key(row) for row in restricted} != {vector_key(row) for row in rays}:
                raise AssertionError(('fresh Regina family ray mismatch', n))
            regina_source.update(full_standard_vertices=len(full),
                                 restricted_standard_vertices=len(restricted),
                                 full_standard_sha256=ray_digest(full))

        ray_records = []
        for parameters, row in zip(parameter_rays(n), expected):
            x, y, z = parameters
            h = max(0, y - a*x, z - a*x)
            census = _native_classification(raw, row, x, h)
            native_queries += 1
            regina_record = None
            if fresh_regina:
                surface = regina.NormalSurface(regina_tri, regina.NormalCoords.Standard,
                                               list(vector_key(row)))
                regina_record = dict(
                    connected=surface.isConnected(), orientable=surface.isOrientable(),
                    euler_characteristic=int(str(surface.eulerChar())),
                    boundary_components=surface.countBoundaries(),
                    compressing_disc=surface.isCompressingDisc(True))
                if (regina_record['connected'], regina_record['orientable'],
                        regina_record['euler_characteristic'],
                        regina_record['boundary_components'],
                        regina_record['compressing_disc']) != (True, True, 1, 1, bool(x)):
                    raise AssertionError(('Regina family topology differs', n, parameters, regina_record))
                regina_queries += 1
            ray_records.append(dict(
                parameters=parameters, shift=h, coordinates=row,
                native_census=census, native_certificate_replayed=True,
                regina=regina_record))

        # These mixed directions test the component statement beyond rays.
        mixed_records = []
        for x, y, z in ((0, 2, 3), (2, a+1, 3*a+1), (3, 4*a, a)):
            row = formula_rows(n, x, y, z)
            h = max(0, y - a*x, z - a*x)
            census = _native_classification(raw, row, x, h)
            native_queries += 1
            mixed_records.append(dict(parameters=(x, y, z), shift=h,
                coordinates=row, native_census=census,
                native_certificate_replayed=True))
        records.append(dict(
            base_tetrahedra=n, tetrahedra=n+2,
            source=source, source_sha256=prepared.source_sha256,
            a=a, b=b, matching_dimension=3,
            ray_count=7, ray_sha256=ray_digest(rays), stats=stats, geometry=metrics,
            native_potential_forms_in_base_offset_gauge=sorted(all_forms),
            active_minimum_forms_in_base_offset_gauge=sorted(active_forms),
            canonical_formula_grid_cases=len(grid),
            rays=ray_records, mixed_directions=mixed_records,
            regina_source=regina_source))
        print('double cap n=', n, 'rays=7, essential=4, inessential=3; exact checks passed', flush=True)
    fast = Path(__file__).resolve().parents[1]
    files = ('planar_sector_research/family_audit.py', 'planar_sector_research/fixtures.py',
             'fastunknot/sector_planar.py', 'fastunknot/sector_sparse.py',
             'fastunknot/sector_planar_verify.py',
             'fastunknot/normal_surface_components.py', 'fastunknot/normal_component_verify.py')
    answer = dict(schema='double-cap-fibonacci-audit-v1', python=platform.python_version(),
        scope='untimed finite verification of an explicit all-size source family',
        source_sha256={name: sha256((fast / name).read_bytes()).hexdigest() for name in files},
        sizes=list(sizes), canonical_formula_grid_cases=formula_cases,
        native_component_queries=native_queries,
        all_native_component_certificates_replayed=True,
        regina_surface_classifications=regina_queries,
        regina_complete_standard_enumerations=len(sizes) if fresh_regina else 0,
        records=records)
    if fresh_regina:
        answer['regina_version'] = regina.versionString()
    return answer, dict(schema='planar-sector-coverage-samples-v1', records=certificates)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--certificates', type=Path)
    parser.add_argument('--sizes', nargs='+', type=int, default=(1, 2, 4, 8))
    parser.add_argument('--fresh-regina', action='store_true')
    args = parser.parse_args()
    answer, certificates = run(args.sizes, fresh_regina=args.fresh_regina)
    certificates_path = args.certificates or args.output.with_name('double_cap_coverage_certificates.json')
    for path, value in ((args.output, answer), (certificates_path, certificates)):
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(json.dumps(value, indent=2, sort_keys=True) + '\n')
    print('COMPLETE', answer['native_component_queries'], 'native component queries,',
          answer['regina_surface_classifications'], 'Regina classifications', flush=True)


if __name__ == '__main__':
    main()
