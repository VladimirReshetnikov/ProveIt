#!/usr/bin/env python3
"""Paired dense/sparse port timings and compressed normal-component capacity.

Run from the package root: python3 experiments/benchmark_geometry.py --fast code
All timings cover complete calls; correctness comparison is outside timing.
"""
import argparse
from collections import defaultdict
from datetime import datetime, timezone
import gc
import hashlib
import json
from pathlib import Path
import platform
import random
import statistics
import sys
import time


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--fast', type=Path, required=True)
    parser.add_argument('--output', type=Path, default=Path('results/geometry_benchmark.json'))
    parser.add_argument('--rounds', type=int, default=5)
    args = parser.parse_args()
    sys.path.insert(0, str(args.fast.resolve()))
    from fastunknot.interval_incidence import analyze_port_incidence
    from fastunknot.sparse_port_incidence import sparse_port_incidence, verify_sparse_port_certificate
    from fastunknot.normal_components import normal_component_inventory, verify_normal_component_certificate
    from fastunknot.normal_surface_orbits import normal_arc_pairings
    from fastunknot.integer_codec import json_safe
    from normal_orbit_research.fixtures import layered_torus

    modules = sorted((args.fast / 'fastunknot').rglob('*.py'))
    def hashes():
        return {str(p.relative_to(args.fast)): hashlib.sha256(p.read_bytes()).hexdigest()
                for p in modules}
    before = hashes()
    rng = random.Random(261009211)
    cases = []
    def add(name, size, pairs, r, style):
        if style == 'disjoint':
            ports = [[(j * size // r, (j + 1) * size // r)] for j in range(r)]
        elif style == 'nested':
            ports = [[(0, (j + 1) * size // r)] for j in range(r)]
        else:
            ports = [[(0, size // 2)] for _ in range(r)]
        cases.append((name, size, pairs, ports, style))
    size = 2 ** 512
    for r in (4, 8, 12):
        add(f'static_disjoint_{r}', size, [], r, 'disjoint')
    add('static_nested_12', size, [], 12, 'nested')
    add('static_identical_12', size, [], 12, 'identical')
    tri, primitive = layered_torus(8)
    for scale, label in ((1, 'meridian'), (2 ** 64, 'parallel')):
        coords = [[scale * x for x in row] for row in primitive]
        n, pairs = normal_arc_pairings(tri, coords)
        for r in (4, 6, 8):
            add(f'{label}_disjoint_{r}', n, pairs, r, 'disjoint')
        add(f'{label}_identical_8', n, pairs, 8, 'identical')

    arms = ['dense', 'dense_control', 'sparse', 'sparse_verified']
    results = []
    for name, n, pairs, ports, style in cases:
        rows, reference = [], None
        for round_index in range(-1, args.rounds):
            order = list(arms)
            rng.shuffle(order)
            for arm in order:
                gc.collect()
                start = time.perf_counter_ns()
                if arm.startswith('dense'):
                    answer = analyze_port_incidence(n, pairs, ports)
                else:
                    answer = sparse_port_incidence(n, pairs, ports,
                                                    record_certificate=arm == 'sparse_verified')
                    if arm == 'sparse_verified':
                        verified = verify_sparse_port_certificate(n, pairs, ports,
                                                                    answer['certificate'])
                        if not verified:
                            raise AssertionError('new certificate failed replay')
                elapsed = time.perf_counter_ns() - start
                if answer['status'] != 'COMPLETE':
                    raise AssertionError('unlimited query incomplete')
                if arm.startswith('dense'):
                    histogram = [[mask, count] for mask, count in enumerate(answer['histogram']) if count]
                else:
                    histogram = [[row['mask'], row['orbits']] for row in answer['histogram']]
                if reference is None:
                    reference = histogram
                if histogram != reference:
                    raise AssertionError(f'dense/sparse mismatch: {name}/{arm}')
                row = dict(round=round_index, arm=arm, seconds=elapsed / 1e9,
                           status=answer['status'], stats=answer['stats'])
                if 'certificate' in answer:
                    row['certificate_bytes'] = len(json.dumps(json_safe(answer['certificate']),
                                                              separators=(',', ':')).encode())
                rows.append(row)
        by_round = defaultdict(dict)
        for row in rows:
            if row['round'] >= 0:
                by_round[row['round']][row['arm']] = row['seconds']
        medians = {arm: statistics.median(row[arm] for row in by_round.values()) for arm in arms}
        ratios = {arm: statistics.median(row['dense'] / row[arm] for row in by_round.values())
                  for arm in arms if arm != 'dense'}
        results.append(dict(name=name, size=hex(n), size_bits=n.bit_length(),
                            pairings=[[p.a, p.b, p.c, p.d, p.reverse] for p in pairs],
                            ports=ports, style=style, histogram=reference, samples=rows,
                            medians=medians, paired_ratios=ratios))
        print(name, json.dumps({'medians': medians, 'ratios': ratios}), flush=True)

    # Capacity records are distinct from comparative timing experiments.
    capacity = []
    for bits in (128, 1024, 4096, 16384):
        tri, meridian = layered_torus(8)
        k, ell = 1 << bits, (1 << bits) + 1
        link = [[1, 1, 1, 1, 0, 0, 0] for _ in meridian]
        coords = [[k * x + ell * y for x, y in zip(a, b)] for a, b in zip(meridian, link)]
        start = time.perf_counter_ns()
        result = normal_component_inventory(tri, coords, record_certificate=True)
        assert verify_normal_component_certificate(tri, coords, result['certificate'])
        elapsed = (time.perf_counter_ns() - start) / 1e9
        assert result['components'] == k + ell
        assert result['distinct_vectors'] == 2
        assert result['compressing_disk_components'] == k
        capacity.append(dict(exponent_bits=bits, elapsed_seconds=elapsed,
            tetrahedra=tri, coordinates=coords, result=result,
            certificate_bytes=len(json.dumps(json_safe(result['certificate']),
                                            separators=(',', ':')).encode())))
        print('normal_capacity', bits, elapsed, flush=True)
    for r in (32, 128, 512):
        scale = 2 ** 1024
        ports = [[(j * scale, (j + 1) * scale)] for j in range(r)]
        start = time.perf_counter_ns()
        result = sparse_port_incidence(r * scale, [], ports, record_certificate=True)
        assert verify_sparse_port_certificate(r * scale, [], ports, result['certificate'])
        elapsed = (time.perf_counter_ns() - start) / 1e9
        assert len(result['histogram']) == r
        capacity.append(dict(ports=r, point_bits=(r * scale).bit_length(),
                             elapsed_seconds=elapsed, stats=result['stats'],
                             output_records=len(result['histogram'])))
        print('port_capacity', r, elapsed, flush=True)
    after = hashes()
    if before != after:
        raise AssertionError('source changed during benchmark')
    output = dict(baseline_commit='9feb4346b4d050b305f825f0f7257f495960822a',
                  created_utc=datetime.now(timezone.utc).isoformat(),
                  python=sys.version, platform=platform.platform(),
                  rounds=args.rounds, seed=261009211,
                  measured_calls=len(cases) * len(arms) * args.rounds,
                  source_sha256=before, results=results, capacity=capacity)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(json_safe(output), indent=2) + '\n')
    print('SAVED', args.output, flush=True)


if __name__ == '__main__':
    main()
