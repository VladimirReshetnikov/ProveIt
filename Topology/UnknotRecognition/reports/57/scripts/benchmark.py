#!/usr/bin/env python3
"""Paired fixed-sector benchmarks. These are not whole-knot timings."""

import argparse
from copy import deepcopy
from hashlib import sha256
import json
from pathlib import Path
import platform
import random
import statistics
import sys
import time

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT/'fast'))
from fibonacci_fixture import fibonacci_torus
from fastunknot.normal_sector import enumerate_sector, discover_in_sector
from fastunknot.normal_sector_verify import dense_sector_model, dense_reference_rays

SEED = 2026100903


def cap(triangulation):
    result = deepcopy(triangulation)
    faces = result['tetrahedra']
    t, f = next((t, f) for t, row in enumerate(faces)
                for f, record in enumerate(row) if record is None)
    permutation = [0]*4
    permutation[f] = 3
    for image, vertex in enumerate(v for v in range(4) if v != f):
        permutation[vertex] = image
    u = len(faces)
    faces.append([None]*4)
    faces[t][f] = dict(tetrahedron=u, permutation=permutation)
    faces[u][3] = dict(tetrahedron=t, permutation=[permutation.index(v) for v in range(4)])
    return result


def digest(value):
    return sha256(json.dumps(value, sort_keys=True, separators=(',', ':')).encode()).hexdigest()


def source_hashes():
    paths = sorted((ROOT/'fast'/'fastunknot').rglob('*.py'))
    paths += [Path(__file__), ROOT/'scripts'/'fibonacci_fixture.py']
    return {str(p.relative_to(ROOT)):sha256(p.read_bytes()).hexdigest() for p in paths}


def ray_call(tri, support, arm):
    if arm.startswith('kernel'):
        rows, stats = enumerate_sector(tri, support, phase='quadrilateral')
    else:
        model = dense_sector_model(tri, support)
        rays = dense_reference_rays(model, 'quadrilateral')
        rows = [row for row, chi in rays.values()]
        stats = dict(matching_nullity=len(model['basis']))
    canonical = sorted(tuple(x for row in vector for x in row) for vector in rows)
    return dict(answer_sha256=digest(canonical), ray_count=len(rows), stats=stats)


def certified_call(tri, support):
    result = discover_in_sector(tri, support)
    if result['status'] != 'DISC_FOUND':
        raise AssertionError(result)
    encoded = json.dumps(result['certificate'], sort_keys=True, separators=(',', ':')).encode()
    return dict(status=result['status'], stats=result['stats'],
                answer_sha256=digest(result['coordinates']),
                certificate_sha256=sha256(encoded).hexdigest(), certificate_bytes=len(encoded),
                maximum_coordinate_bits=max(x.bit_length() for row in result['coordinates'] for x in row))


def measure(family, n, tri, support, arms, rounds, rng, query):
    records = []
    for repeat in range(-1, rounds):
        order = list(arms)
        rng.shuffle(order)
        for arm in order:
            started = time.perf_counter()
            value = query(arm)
            elapsed = time.perf_counter()-started
            records.append(dict(repeat=repeat, warmup=repeat == -1,
                                arm=arm, seconds=elapsed, **value))
        print(f'{family} t={n} round={repeat} complete', flush=True)
    assert len({x['answer_sha256'] for x in records}) == 1
    medians = {arm:statistics.median(x['seconds'] for x in records
                                   if x['arm'] == arm and not x['warmup']) for arm in arms}
    result = dict(family=family, tetrahedra=n, support=[list(x) for x in support],
                  triangulation=tri, rounds=rounds, records=records, median_seconds=medians)
    if family == 'sparse_boundary_caps':
        paired = []
        for repeat in range(rounds):
            row = {x['arm']:x['seconds'] for x in records if x['repeat'] == repeat}
            paired.extend([row['dense_A']/row['kernel_A'], row['dense_B']/row['kernel_B']])
        result['paired_dense_over_kernel'] = paired
        result['median_paired_dense_over_kernel'] = statistics.median(paired)
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, default=ROOT/'results'/'benchmarks.json')
    parser.add_argument('--large', action='store_true', help='include three rounds at dense t=128')
    args = parser.parse_args()
    rng = random.Random(SEED)
    before = source_hashes()
    result = dict(schema='normal-sector-benchmark-v1', seed=SEED,
                  python=platform.python_version(), platform=platform.platform(),
                  source_sha256=before, records=[],
                  scope='Fixed compatible sectors, including source validation. Sparse controls '
                  'compare the new exact Q-ray query with the independent dense Python reference '
                  'for the identical ray set; they do not compare with Regina or old whole-knot '
                  'recognition. Dense Fibonacci calls include discovery, certificate creation, '
                  'serialization and native independent disc replay. Fixture generation is excluded.')
    tri = fibonacci_torus(1)['triangulation']
    for n in (4, 8, 16, 32, 64, 128):
        while len(tri['tetrahedra']) < n:
            tri = cap(tri)
        support = [(0, 2)]
        case = measure('sparse_boundary_caps', n, tri, support,
                       ['kernel_A','kernel_B','dense_A','dense_B'], 5, rng,
                       lambda arm: ray_call(tri, support, arm))
        result['records'].append(case)
        args.output.write_text(json.dumps(result, indent=2)+'\n')
    sizes = [4, 8, 16, 32, 64] + ([128] if args.large else [])
    for n in sizes:
        fixture = fibonacci_torus(n)
        tri = fixture['triangulation']
        support = [(i, 2) for i in range(n)]
        case = measure('dense_fibonacci_certified', n, tri, support,
                       ['new_A','new_B'], 3 if n == 128 else 5, rng,
                       lambda arm: certified_call(tri, support))
        result['records'].append(case)
        args.output.write_text(json.dumps(result, indent=2)+'\n')
    after = source_hashes()
    assert before == after
    result['source_hashes_unchanged'] = True
    all_calls = [r for c in result['records'] for r in c['records']]
    result['measured_calls'] = sum(not r['warmup'] for r in all_calls)
    result['warmup_calls'] = sum(r['warmup'] for r in all_calls)
    args.output.write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k not in ('records','source_sha256')}, indent=2))


if __name__ == '__main__':
    main()
