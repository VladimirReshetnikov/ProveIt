"""Reproduce independent normal-disc audits and a controlled local benchmark.

Run from fast/: python -m certificate_research.benchmark --output DIR [--native]
The standard-library certificate runs always execute.  --native additionally
uses Regina for independent face-pairing and surface cross-checks; its costly
disc predicate runs in a process with explicit time and memory allowances.
"""
import argparse
from copy import deepcopy
import hashlib
import json
import os
from pathlib import Path
import platform
import random
from statistics import median
import subprocess
import sys
from time import perf_counter

from fastunknot.normal_disk_certificate import (
    NormalDiskError, _prepare, audit_normal_disk_certificate,
    normal_disk_certificate, verify_normal_disk_certificate)
from .fixtures import (export_triangulation, fibonacci, layered_torus,
                       regina_surface, regina_triangulation)


def native_worker(tetrahedra):
    """The timer excludes conversion; the checker timer includes validation."""
    import resource
    resource.setrlimit(resource.RLIMIT_AS, (768 * 1024**2, 768 * 1024**2))
    try:
        raw, coordinates = layered_torus(tetrahedra)
        triangulation = regina_triangulation(raw)
        surface = regina_surface(triangulation, coordinates)
        start = perf_counter()
        answer = surface.isCompressingDisc(True)
        result = dict(status='COMPLETE', answer=answer, seconds=perf_counter()-start)
    except (MemoryError, RuntimeError) as error:
        result = dict(status='RESOURCE_FAILURE', error=type(error).__name__)
    print(json.dumps(result), flush=True)


def native_query(tetrahedra, timeout=3.0):
    start = perf_counter()
    try:
        proc = subprocess.run(
            [sys.executable, '-m', 'certificate_research.benchmark',
             '--native-worker', str(tetrahedra)], capture_output=True,
            text=True, timeout=timeout, check=False)
    except subprocess.TimeoutExpired:
        return dict(status='TIME_LIMIT', process_seconds=perf_counter()-start)
    try:
        result = json.loads(proc.stdout)
    except ValueError:
        result = dict(status='WORKER_FAILURE', exit_code=proc.returncode)
    result['process_seconds'] = perf_counter()-start
    if result['status'] == 'COMPLETE':
        assert result['answer'] is True
    return result


def random_manifold_audit(count=1200):
    """Compare independently reconstructed links with Regina's topology API."""
    import regina
    rng, accepted, oracle_accepted = random.Random(202610084), 0, 0
    samples = []
    for case in range(count):
        n = 1 + case % 5
        faces = [(t, f) for t in range(n) for f in range(4)]
        rng.shuffle(faces)
        raw = {'tetrahedra': [[None] * 4 for _ in range(n)]}
        pair_count = rng.randrange(len(faces)//2 + 1)
        for _ in range(pair_count):
            t, f = faces.pop(); u, g = faces.pop()
            other = [v for v in range(4) if v != g]
            rng.shuffle(other)
            permutation = []
            for vertex in range(4):
                permutation.append(g if vertex == f else other.pop())
            inverse = [permutation.index(v) for v in range(4)]
            raw['tetrahedra'][t][f] = dict(tetrahedron=u, permutation=permutation)
            raw['tetrahedra'][u][g] = dict(tetrahedron=t, permutation=inverse)
        native = regina_triangulation(raw)
        expected = (native.isValid() and native.isOrientable() and
                    native.isConnected() and not native.isIdeal() and
                    native.countBoundaryComponents() == 1 and
                    int(str(native.boundaryComponent(0).eulerChar())) == 0)
        try:
            _prepare(raw, lambda: None)
            actual = True
        except NormalDiskError:
            actual = False
        if actual != expected:
            raise AssertionError(dict(case=case, triangulation=raw,
                                      checked=actual, native=expected))
        accepted += actual
        oracle_accepted += expected
        if actual:
            samples.append(raw)
    return dict(cases=count, accepted=accepted, oracle_accepted=oracle_accepted,
                mismatches=0, seed=202610084, accepted_inputs=samples)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path)
    parser.add_argument('--native', action='store_true')
    parser.add_argument('--native-worker', type=int)
    args = parser.parse_args()
    if args.native_worker is not None:
        native_worker(args.native_worker)
        return
    if args.output is None:
        parser.error('--output is required')
    args.output.mkdir(parents=True, exist_ok=True)
    rng, rows = random.Random(202610085), []
    native_sizes = {6, 10, 14, 18, 22}
    for size in (1, 2, 6, 10, 14, 18, 22, 32, 64, 128, 256):
        raw, coordinates = layered_torus(size)
        certificate = normal_disk_certificate(raw, coordinates)
        assert certificate is not None
        evidence = audit_normal_disk_certificate(raw, certificate)
        fixture = dict(triangulation=raw, certificate=certificate,
                       input_family='Fibonacci layered solid torus',
                       correspondence='No input PD is part of this fixture.')
        encoded = (json.dumps(fixture, sort_keys=True, separators=(',', ':'))+'\n').encode()
        (args.output/f'layered_torus_{size}.json').write_bytes(encoded)
        samples = []
        for repetition in range(6):
            order = ['checker', 'checker_control']
            if args.native and size in native_sizes:
                order.append('regina')
            rng.shuffle(order)
            results = {}
            for arm in order:
                if arm == 'regina':
                    results[arm] = native_query(size)
                else:
                    start = perf_counter()
                    assert verify_normal_disk_certificate(raw, certificate)
                    results[arm] = dict(status='COMPLETE', seconds=perf_counter()-start)
            if repetition:
                samples.append(dict(order=order, results=results))
        medians = {arm: median(s['results'][arm]['seconds'] for s in samples)
                   for arm in order if all(s['results'][arm]['status'] == 'COMPLETE'
                                           for s in samples)}
        row = dict(tetrahedra=size, evidence=evidence, certificate_bytes=len(encoded),
                   sha256=hashlib.sha256(encoded).hexdigest(), samples=samples,
                   completed={arm: sum(s['results'][arm]['status'] == 'COMPLETE'
                                       for s in samples) for arm in order},
                   median_seconds=medians)
        rows.append(row)
        print(size, evidence['normal_disks'], medians, row['completed'], flush=True)

    # These are independent mutation checks of externally visible claims.
    raw, coordinates = layered_torus(8)
    certificate = normal_disk_certificate(raw, coordinates)
    rejected = 0
    for case in range(128):
        bad = deepcopy(certificate)
        t, q = rng.randrange(8), rng.randrange(7)
        bad['normal_coordinates'][t][q] += 1 + case % 3
        if verify_normal_disk_certificate(raw, bad):
            raise AssertionError('single-coordinate mutation was accepted')
        rejected += 1
    boundary_parallel = deepcopy(certificate)
    boundary_parallel['normal_coordinates'] = [[1, 1, 1, 1, 0, 0, 0] for _ in range(8)]
    assert not verify_normal_disk_certificate(raw, boundary_parallel)
    details = dict(python=sys.version, platform=platform.platform(), seed=202610085,
                   measured_rounds=5, excluded_warmups=1, rows=rows,
                   coordinate_mutations_rejected=rejected,
                   native_timeout_seconds=3, native_address_space_bytes=768*1024**2,
                   scope='Supplied-surface predicate, not knot recognition or surface discovery.',
                   timer='Checker includes finite-manifold validation, matching, rank and topology; '
                         'native predicate excludes process startup and input construction.',
                   censoring='Only all-complete arms receive completion medians; resource limits '
                             'are never used as completion-speedup denominators.')
    if args.native:
        import regina
        from importlib.metadata import version
        details['regina'] = dict(engine=regina.versionString(), distribution=version('regina'))
        details['manifold_crosscheck'] = random_manifold_audit()
        for size in range(1, 13):
            raw, coordinates = layered_torus(size)
            tri = regina.Triangulation3()
            tri.insertLayeredSolidTorus(fibonacci(size+1), fibonacci(size+2))
            assert export_triangulation(tri) == raw
            surface = regina_surface(tri, coordinates)
            assert surface.isConnected() and int(str(surface.eulerChar())) == 1
        details['independent_native_layered_checks'] = 12
    (args.output/'normal_disk_benchmark.json').write_text(json.dumps(details, indent=2)+'\n')


if __name__ == '__main__':
    main()
