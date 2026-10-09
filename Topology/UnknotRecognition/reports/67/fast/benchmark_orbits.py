"""Controlled binary interval and supplied-surface topology measurements.

Run from fast/: python -B benchmark_orbits.py --output results/orbits.json
Includes shuffled A/A controls, one warmup and independent finite expectations.
No whole-knot performance inference is made from these component measurements.
"""
import argparse
import hashlib
import json
from pathlib import Path
import platform
import random
from statistics import median
import subprocess
import time

from fastunknot.interval_orbits import IntervalPairing, count_orbits
from fastunknot.normal_surface_orbits import normal_arc_pairings, normal_surface_topology
from normal_orbit_research.fixtures import layered_torus


def literal_components(n, pairs):
    """Independent parity graph; only used on materialisable inputs."""
    graph = [[] for _ in range(n)]
    for p in pairs:
        for x in range(p.a, p.b + 1):
            y = p.a + p.d - x if p.reverse else x + p.c - p.a
            graph[x].append((y, p.reverse))
            graph[y].append((x, p.reverse))
    labels = {}
    consistent = inconsistent = 0
    for start in range(n):
        if start in labels:
            continue
        labels[start] = 0
        todo, good = [start], True
        while todo:
            x = todo.pop()
            for y, sign in graph[x]:
                target = labels[x] ^ sign
                if y in labels:
                    good &= labels[y] == target
                else:
                    labels[y] = target
                    todo.append(y)
        consistent += good
        inconsistent += not good
    return consistent, inconsistent


def safe(value):
    if type(value) is int and value.bit_length() > 256:
        return hex(value)
    if isinstance(value, dict):
        return {key: safe(item) for key, item in value.items()}
    if isinstance(value, (list, tuple)):
        return [safe(item) for item in value]
    return value


def measured(query, expected, rng, rounds):
    times = {arm: [] for arm in ('aht', 'fine_wilf', 'fine_wilf_AA')}
    orders, outputs = [], {}
    for trial in range(-1, rounds):
        order = list(times)
        rng.shuffle(order)
        orders.append(order)
        for arm in order:
            start = time.perf_counter_ns()
            result = query('aht' if arm == 'aht' else 'fine_wilf')
            elapsed = (time.perf_counter_ns() - start) / 1e9
            expected(result)
            if trial >= 0:
                times[arm].append(elapsed)
            outputs[arm] = result
    return dict(seconds=times, medians={arm: median(values) for arm, values in times.items()},
                paired_speedup=median(a / b for a, b in zip(times['aht'], times['fine_wilf'])),
                paired_AA=median(a / b for a, b in zip(times['fine_wilf_AA'], times['fine_wilf'])),
                orders=orders, outputs=safe(outputs))


def interval_case(name, n, pairs, expected, rng, rounds):
    def query(rule):
        result = count_orbits(n, pairs, periodic_rule=rule)
        return dict(complete=result.complete, orbits=result.orbits,
                    cycles=result.cycles, stats=result.stats)
    def check(result):
        assert result['complete'] and result['orbits'] == expected
    row = measured(query, check, rng, rounds)
    row.update(family=name, n_bits=n.bit_length(), pairings=len(pairs),
               input_sha256=hashlib.sha256(json.dumps(safe([n, [
                   [p.a, p.b, p.c, p.d, p.reverse] for p in pairs]])).encode()).hexdigest())
    return row


def surface_case(size, bits, rng, rounds):
    raw, coords = layered_torus(size)
    scale = 1 << bits
    coords = [[scale * v for v in row] for row in coords]
    def query(rule):
        return normal_surface_topology(raw, coords, periodic_rule=rule)
    def check(result):
        assert result['status'] == 'COMPLETE'
        assert result['components'] == result['orientable_components'] == scale
        assert result['boundary_components'] == result['euler_characteristic'] == scale
        assert result['nonorientable_components'] == 0
        assert result['compressing_disk'] == (scale == 1)
    row = measured(query, check, rng, rounds)
    n, pairs = normal_arc_pairings(raw, coords)
    row.update(tetrahedra=size, scale_bits=bits + 1, explicit_points=safe(n),
               explicit_attempted=n <= 100000)
    if row['explicit_attempted']:
        start = time.perf_counter_ns()
        a, b = literal_components(n, pairs)
        row['explicit_seconds'] = (time.perf_counter_ns() - start) / 1e9
        assert a + b == scale
    return row


def source_hashes():
    root = Path(__file__).resolve().parent
    names = ['benchmark_orbits.py', 'fastunknot/interval_orbits.py',
             'fastunknot/normal_surface_orbits.py', 'fastunknot/integer_codec.py',
             'normal_orbit_research/fixtures.py']
    return {name: hashlib.sha256((root / name).read_bytes()).hexdigest() for name in names}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--rounds', type=int, default=5)
    args = parser.parse_args()
    if args.rounds < 1:
        parser.error('--rounds must be positive')
    before = source_hashes()
    rng = random.Random(261008171)
    data = dict(schema='native_orbit_controls_v1', python=platform.python_version(),
                platform=platform.platform(), rounds=args.rounds, warmups=1,
                seed=261008171, checkout=subprocess.check_output(
                    ['git', 'rev-parse', 'HEAD'], text=True).strip(),
                notes=['All arms use the same native kernel; only periodic merge threshold differs.',
                       'Input construction and validation of results are outside timings.',
                       'Surface timings include manifold/vector validation and all three orbit queries.',
                       'Explicit controls count connectivity only, once, with a 100000-point cap.',
                       'Large integers in output use hexadecimal strings.',
                       'These are component queries, not full recognition timings.'],
                intervals=[], surfaces=[])
    p = (1 << 512) + 1
    for k in (8, 16, 32, 64, 128):
        pairs = [IntervalPairing(i*p, (i+1)*p-1, (i+1)*p, (i+2)*p-1) for i in range(k)]
        row = interval_case('adjacent_periodic_chain', (k+1)*p, pairs, p, rng, args.rounds)
        assert row['outputs']['aht']['cycles'] == k + 1
        assert row['outputs']['fine_wilf']['cycles'] == 2
        data['intervals'].append(row)
    fixtures_rng = random.Random(2610081701)
    for template in range(6):
        n, k = 23 + template, 8 + template
        pairs = []
        for _ in range(k):
            width = fixtures_rng.randrange(1, n+1)
            a, c = (fixtures_rng.randrange(n-width+1) for _ in range(2))
            pairs.append(IntervalPairing(a, a+width-1, c, c+width-1,
                                         bool(fixtures_rng.getrandbits(1))))
        consistent, inconsistent = literal_components(n, pairs)
        for bits in (16, 256, 4096, 16384):
            scale = (1 << bits) + 1
            lifted = [IntervalPairing(p.a*scale, (p.b+1)*scale-1,
                                      p.c*scale, (p.d+1)*scale-1, p.reverse) for p in pairs]
            row = interval_case('scaled_signed_quotient', n*scale, lifted,
                consistent*scale + inconsistent*((scale+1)//2), rng, args.rounds)
            row.update(template=template, scale_bits=bits,
                       consistent=consistent, inconsistent=inconsistent)
            data['intervals'].append(row)
    for size in (4, 8, 12, 16, 20, 32, 64, 128):
        data['surfaces'].append(surface_case(size, 0, rng, args.rounds))
        print('completed surface', size, flush=True)
    for bits in (0, 32, 128, 500, 2000):
        data['surfaces'].append(surface_case(3, bits, rng, args.rounds))
    after = source_hashes()
    assert before == after, 'measured source changed during benchmark'
    data.update(source_sha256=before, source_sha256_after=after,
                measured_sources_unchanged=True)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(data, indent=2) + '\n')


if __name__ == '__main__':
    main()
