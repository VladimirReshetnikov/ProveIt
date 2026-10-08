"""Reproduce certified cocycle-seed measurements, including genuine manifolds.

Run from fast/: python benchmark_cocycle_seed.py --output results/cocycle_seed.json
Add --regina to audit finite trefoil/figure-eight exteriors if Regina is installed.
The archive02 adapter audit is used when that report is present in the repository.
The product solid-torus family isolates binary-height scaling; it is deliberately
constructed by gauge perturbation and is not a random-knot performance corpus.
"""

from __future__ import annotations

import argparse
import importlib
import json
from math import gcd
from pathlib import Path
import platform
import random
import sys
import time

from fastunknot.cocycle_seed import (
    face_pairing_data, minimize_disc_seed, optimize_triangulated_cocycle,
    check_seed_certificate, check_glued_normal_coordinates,
)


def product_solid_torus(steps=3, amplitude=0, seed=2718):
    """Explicit staircase triangulation of triangle x a steps-edge circle.

    Its 3*steps tetrahedra triangulate D^2 x S^1. Local heights are the pullback
    of a primitive cocycle on the circle, plus an integral GLOBAL vertex
    potential. Therefore every amplitude gives the same primitive class.
    """
    if type(steps) is not int or steps < 3 or type(amplitude) is not int:
        raise ValueError('steps must be >=3 and amplitude integral')
    tetrahedra, heights = [], []
    rng = random.Random(seed)
    perturbation = [rng.randrange(-11, 12) * amplitude for _ in range(3 * steps)]
    for k in range(steps):
        bottom, top = [3 * k + i for i in range(3)], [3 * ((k + 1) % steps) + i
                                                       for i in range(3)]
        weight = 1 if k == steps - 1 else 0
        prism = ((bottom[0], bottom[1], bottom[2], top[2]),
                 (bottom[0], bottom[1], top[1], top[2]),
                 (bottom[0], top[0], top[1], top[2]))
        top_set = set(top)
        for tet in prism:
            tetrahedra.append(tet)
            heights.append(tuple((weight if v in top_set else 0) + perturbation[v]
                                 for v in tet))
    gluings = [[None] * 4 for _ in tetrahedra]
    seen = {}
    for t, tet in enumerate(tetrahedra):
        for face in range(4):
            key = tuple(sorted(tet[i] for i in range(4) if i != face))
            if key not in seen:
                seen[key] = (t, face)
                continue
            s, other_face = seen.pop(key)
            p = tuple(other_face if i == face else tetrahedra[s].index(tet[i])
                      for i in range(4))
            inverse = tuple(p.index(i) for i in range(4))
            gluings[t][face], gluings[s][other_face] = (s, p), (t, inverse)
    return tuple(tuple(row) for row in gluings), tuple(heights)


def load_archive_triangulation():
    archive = Path(__file__).resolve().parent.parent / 'reports' / '02'
    if not (archive / 'unknotlab' / 'normal.py').exists():
        return None
    if str(archive) not in sys.path:
        sys.path.insert(0, str(archive))
    return importlib.import_module('unknotlab.normal').Triangulation


def regina_triangulation(regina, gluings):
    pairs = []
    for t, row in enumerate(gluings):
        for f, pairing in enumerate(row):
            if pairing is not None:
                s, p = pairing
                if (t, f) < (s, p[f]):
                    pairs.append((t, f, s, regina.Perm4(*p)))
    return regina.Triangulation3.fromGluings(len(gluings), pairs)


def regina_gluings(tri):
    rows = []
    for t in range(tri.size()):
        tet = tri.tetrahedron(t)
        row = []
        for face in range(4):
            adjacent = tet.adjacentTetrahedron(face)
            if adjacent is None:
                row.append(None)
            else:
                p = tet.adjacentGluing(face)
                row.append((adjacent.index(), tuple(p[i] for i in range(4))))
        rows.append(tuple(row))
    return tuple(rows)


def regina_surface_summary(regina, triangulation, coordinates):
    surface = regina.NormalSurface(triangulation, regina.NormalCoords.Standard,
                                   [value for row in coordinates for value in row])
    return {'manifold_valid': triangulation.isValid(),
            'manifold_orientable': triangulation.isOrientable(),
            'manifold_ideal': triangulation.isIdeal(),
            'homology': str(triangulation.homology()),
            'surface_connected': surface.isConnected(),
            'surface_orientable': surface.isOrientable(),
            'surface_euler_characteristic': str(surface.eulerChar()),
            'surface_has_real_boundary': surface.hasRealBoundary(),
            'surface_boundary_components': surface.countBoundaries()}


def run(include_regina=False):
    result = {'schema': 'fastunknot.cocycle-seed-benchmark.v1',
              'python': platform.python_version(), 'cases': [],
              'scope': 'restricted normal-seed optimization, not unknot recognition timing'}
    regina = importlib.import_module('regina') if include_regina else None
    if regina is not None:
        regina.RandomEngine.reseedWithDefault()
        result['regina_version'] = regina.versionString()
    for steps, bits in ((3, 0), (3, 16), (3, 256), (3, 4096),
                        (8, 16), (16, 16), (32, 16)):
        amplitude = 0 if bits == 0 else (1 << bits) + 17
        gluings, heights = product_solid_torus(steps, amplitude)
        gluings, vertices, heights = face_pairing_data(gluings, heights)
        started = time.perf_counter()
        certificate = minimize_disc_seed(vertices, heights)
        elapsed = time.perf_counter() - started
        verify_start = time.perf_counter()
        check_seed_certificate(vertices, heights, certificate)
        check_glued_normal_coordinates(gluings, certificate.normal_coordinates)
        verify_elapsed = time.perf_counter() - verify_start
        record = {'name': f'product_torus_{steps}_heightbits_{bits}',
                  'manifold': 'D^2 x S^1 by explicit product construction',
                  'class': 'primitive circle generator plus exact vertex coboundary',
                  'seconds': elapsed, 'verification_seconds': verify_elapsed,
                  'initial_disc_count': certificate.initial_disc_count,
                  'optimal_disc_count': certificate.disc_count,
                  'statistics': certificate.statistics,
                  'certificate': certificate.as_dict()}
        if regina is not None:
            tri = regina_triangulation(regina, gluings)
            record['regina'] = regina_surface_summary(regina, tri,
                                                     certificate.normal_coordinates)
        result['cases'].append(record)
    # This also demonstrates an input where binary coordinate growth is
    # unavoidable and the vertex gauge has no freedom: all corners share v.
    huge = 1 << 4096
    vertices, heights = ((0, 0, 0, 0),), ((0, huge, 3 * huge, 2 * huge),)
    started = time.perf_counter()
    certificate = minimize_disc_seed(vertices, heights)
    result['one_vertex_binary_case'] = {
        'seconds': time.perf_counter() - started,
        'initial_disc_bits': certificate.initial_disc_count.bit_length(),
        'optimal_disc_bits': certificate.disc_count.bit_length(),
        'statistics': certificate.statistics,
        'scope': 'local optimizer input; no manifold is asserted for this one row'}
    if regina is not None:
        Triangulation = load_archive_triangulation()
        if Triangulation is None:
            result['finite_exterior_audit'] = 'archive02 triangulation validator unavailable'
        else:
            exterior_records = []
            for name, tri in (('trefoil', regina.ExampleLink.trefoil().complement()),
                              ('figure_eight', regina.Example3.figureEight())):
                tri.idealToFinite()
                gluings = regina_gluings(tri)
                validated = Triangulation(gluings)
                basis = validated.rational_cohomology_basis()
                if len(basis) != 1:
                    raise ArithmeticError('named knot exterior does not have rank-one H^1')
                started = time.perf_counter()
                certificate, surface = optimize_triangulated_cocycle(validated, basis[0])
                elapsed = time.perf_counter() - started
                record = {'name': name, 'tetrahedra': tri.size(),
                          'vertices': tri.countVertices(),
                          'finite_triangulation_isosig': tri.isoSig(),
                          'gluings': gluings,
                          'initial_tree_gauge_cocycle': basis[0],
                          'tree_gauge_coordinate_gcd': gcd(*basis[0]),
                          'certificate': certificate.as_dict(),
                          'provenance': 'Regina named example, idealToFinite, '
                                        'archive02 exact tree-gauge rational cohomology basis',
                          'seconds': elapsed,
                          'initial_disc_count': certificate.initial_disc_count,
                          'optimal_disc_count': certificate.disc_count,
                          'statistics': certificate.statistics,
                          'regina': regina_surface_summary(regina, tri, surface.coordinates)}
                exterior_records.append(record)
            result['finite_exterior_audit'] = exterior_records
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--regina', action='store_true')
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    result = run(args.regina)
    text = json.dumps(result, indent=2)
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(text + '\n')
        print(json.dumps({'output': str(args.output), 'cases': len(result['cases'])}))
    else:
        print(text)


if __name__ == '__main__':
    main()
