"""Reproducible structural and elapsed-time benchmarks for interval orbits.

Run from fast/: python interval_research/benchmark.py
Timings are observations; operation counts and expected values are exact.
"""

import argparse
import hashlib
import json
from pathlib import Path
import platform
import random
import statistics
import sys
import time

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from fastunknot.interval_orbits import IntervalPairing, count_orbits


def parity_components(n, pairs):
    """Independent small-graph computation for symbolic scaling checks."""
    graph = [[] for _ in range(n)]
    for p in pairs:
        for x in range(p.a, p.b + 1):
            y = p.a + p.d - x if p.reverse else x + p.c - p.a
            graph[x].append((y, int(p.reverse)))
            graph[y].append((x, int(p.reverse)))
    labels = {}
    a = b = 0
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
        a += int(good)
        b += int(not good)
    return a, b


def explicit_count(n, pairs):
    parent = list(range(n))

    def find(x):
        while parent[x] != x:
            parent[x] = parent[parent[x]]
            x = parent[x]
        return x

    for p in pairs:
        for x in range(p.a, p.b + 1):
            y = p.a + p.d - x if p.reverse else x + p.c - p.a
            parent[find(x)] = find(y)
    return sum(find(x) == x for x in range(n))


def timed(n, pairs, expected, rule, repetitions):
    elapsed = []
    for _ in range(repetitions):
        start = time.perf_counter_ns()
        result = count_orbits(n, pairs, periodic_rule=rule)
        elapsed.append((time.perf_counter_ns() - start) / 1e9)
        if not result.complete or result.orbits != expected:
            raise AssertionError('compressed count disagrees with independent expectation')
    return {'rule': rule, 'seconds_median': statistics.median(elapsed),
            'seconds_all': elapsed, 'cycles': result.cycles,
            'stats': {key: (hex(value) if value.bit_length() > 256 else value)
                      for key, value in result.stats.items()},
            'n_bits': n.bit_length(), 'k': len(pairs),
            'orbit_count_hex': hex(expected),
            'input_sha256': hashlib.sha256(repr((hex(n), [
                (hex(p.a), hex(p.b), hex(p.c), hex(p.d), p.reverse)
                for p in pairs])).encode()).hexdigest()}


def run(repetitions):
    rows = []
    # The original merger requires 2*p overlap; adjacent supports share p.
    # Consequently its cycle count is k+1, while the sharp rule needs 2.
    p = (1 << 512) + 1
    for k in (8, 16, 32, 64, 128):
        pairs = [IntervalPairing(i * p, (i + 1) * p - 1,
                                (i + 1) * p, (i + 2) * p - 1)
                 for i in range(k)]
        for rule in ('aht', 'fine_wilf'):
            row = timed((k + 1) * p, pairs, p, rule, repetitions)
            row['family'] = 'adjacent_periodic_chain'
            expected_cycles = k + 1 if rule == 'aht' else 2
            if row['cycles'] != expected_cycles:
                raise AssertionError('periodic-chain cycle formula failed')
            rows.append(row)
    # A tiny independent parity graph determines arbitrarily large cases.
    rng = random.Random(2610081701)
    for template in range(6):
        n, k = 23 + template, 8 + template
        pairs = []
        for _ in range(k):
            width = rng.randrange(1, n + 1)
            a, c = rng.randrange(n - width + 1), rng.randrange(n - width + 1)
            pairs.append(IntervalPairing(a, a + width - 1, c, c + width - 1,
                                         bool(rng.getrandbits(1))))
        consistent, inconsistent = parity_components(n, pairs)
        for bits in (16, 64, 256, 1024, 4096, 16384):
            scale = (1 << bits) + 1
            expanded = [IntervalPairing(p.a * scale, (p.b + 1) * scale - 1,
                                       p.c * scale, (p.d + 1) * scale - 1,
                                       p.reverse) for p in pairs]
            expected = consistent * scale + inconsistent * ((scale + 1) // 2)
            row = timed(n * scale, expanded, expected, 'fine_wilf', repetitions)
            row.update(family='scaled_signed_quotient', template=template,
                       scale_bits=bits, quotient_consistent=consistent,
                       quotient_inconsistent=inconsistent)
            rows.append(row)
    # Direct union-find baselines are restricted to actually materialisable N.
    for p in (100, 10000, 100000):
        k = 10
        pairs = [IntervalPairing(i * p, (i + 1) * p - 1,
                                (i + 1) * p, (i + 2) * p - 1)
                 for i in range(k)]
        row = timed((k + 1) * p, pairs, p, 'fine_wilf', repetitions)
        start = time.perf_counter_ns()
        actual = explicit_count((k + 1) * p, pairs)
        seconds = (time.perf_counter_ns() - start) / 1e9
        if actual != p:
            raise AssertionError('explicit oracle failed on periodic chain')
        row.update(family='explicit_comparison', n=(k + 1) * p,
                   explicit_seconds=seconds,
                   explicit_to_compressed_ratio=seconds / row['seconds_median'])
        rows.append(row)
    return rows


def source_hashes():
    root = Path(__file__).resolve().parents[1]
    paths = (root / 'fastunknot' / 'interval_orbits.py', Path(__file__).resolve())
    return {str(path.relative_to(root)): hashlib.sha256(path.read_bytes()).hexdigest()
            for path in paths}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--repetitions', type=int, default=3)
    parser.add_argument('--output', type=Path,
                        default=Path(__file__).resolve().with_name('results.json'))
    args = parser.parse_args()
    if args.repetitions < 1:
        parser.error('--repetitions must be positive')
    frozen = source_hashes()
    report = {'schema': 'interval_orbit_benchmarks_v1',
              'python': platform.python_version(), 'platform': platform.platform(),
              'seed': 2610081701, 'repetitions': args.repetitions,
              'notes': ['No GPL implementation or third-party orbit code used.',
                        'Timings include count computation, exclude input construction.',
                        'Explicit comparison uses one DSU timing per instance.',
                        'Integer statistics longer than 256 bits use hexadecimal strings.',
                        'Huge expected counts come from tiny independent parity graphs.'],
              'rows': run(args.repetitions)}
    after = source_hashes()
    if after != frozen:
        raise ArithmeticError('source changed while interval benchmark was running')
    report.update(source_sha256=frozen, source_sha256_after=after,
                  measured_sources_unchanged=True,
                  baseline_commit='58ee11a97d5fd7f21647c57eefaf3ecc007931d6')
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps({'rows': len(report['rows']), 'output': str(args.output)}))


if __name__ == '__main__':
    main()
