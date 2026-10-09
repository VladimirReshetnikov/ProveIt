#!/usr/bin/env python3
"""Reproduce the independent weighted replay checker's deterministic audit.

This checks abstract interval-equivalence systems, not knot diagrams. The
workload is fixed: 2,500 small literal union-find comparisons, periodic proof
mutations, one 20,002-bit endpoint fixture, and producer-disabled replay.

Example, from the fast directory::

    python weighted_research/checker_audit.py \
        --output results/weighted_checker_audit_20261009.json
"""

import argparse
import copy
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import platform
import random
import sys
import time

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))

from fastunknot.interval_orbits import IntervalPairing
from fastunknot.weighted_orbits import weighted_orbit_histogram
from fastunknot.weighted_orbit_verify import verify_weighted_orbit_certificate
from fastunknot.integer_codec import json_safe


SEED = 2610091843
CASES = 2500


def literal(size, pairs, weights, dimension):
    """Expand this deliberately small input and sum literal graph components."""
    parent = list(range(size))

    def root(point):
        while parent[point] != point:
            parent[point] = parent[parent[point]]
            point = parent[point]
        return point

    for pair in pairs:
        for point in range(pair.a, pair.b + 1):
            parent[root(point)] = root(pair.image(point))
    values = [[0] * dimension for _ in range(size)]
    for lo, hi, weight in weights:
        for point in range(lo, hi):
            for j in range(dimension):
                values[point][j] += weight[j]
    sums = {}
    for point, value in enumerate(values):
        out = sums.setdefault(root(point), [0] * dimension)
        for j in range(dimension):
            out[j] += value[j]
    histogram = {}
    for value in sums.values():
        key = tuple(value)
        histogram[key] = histogram.get(key, 0) + 1
    return [dict(weight=list(value), orbits=count)
            for value, count in sorted(histogram.items())]


def source_metadata():
    modules = ('interval_orbits.py', 'interval_orbit_verify.py', 'integer_codec.py',
               'weighted_orbits.py', 'weighted_orbit_verify.py')
    return dict(
        timestamp_utc=datetime.now(timezone.utc).isoformat(),
        python=platform.python_version(), platform=platform.platform(),
        driver_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        source_sha256={name: hashlib.sha256((ROOT / 'fastunknot' / name).read_bytes()).hexdigest()
                       for name in modules},
    )


def run():
    started = time.perf_counter()
    rng = random.Random(SEED)
    tamper_checks = 0
    stats = dict(reflection_pushes=0, translation_pushes=0, replay_events=0)
    exemplar = None
    for case in range(CASES):
        size = rng.randrange(41)
        dimension = rng.randrange(1, 6)
        pairs = []
        if size:
            for _ in range(rng.randrange(18)):
                width = rng.randrange(1, size + 1)
                a, c = rng.randrange(size - width + 1), rng.randrange(size - width + 1)
                pairs.append(IntervalPairing(a, a + width - 1, c, c + width - 1,
                                             bool(rng.randrange(2))))
        weights = []
        for _ in range(rng.randrange(12)):
            a, b = sorted((rng.randrange(size + 1), rng.randrange(size + 1)))
            value = tuple(rng.randrange(-9, 10) for _ in range(dimension))
            weights.append((a, b, value))
        result = weighted_orbit_histogram(size, pairs, weights, dimension=dimension,
                                          record_certificate=True)
        assert result['histogram'] == literal(size, pairs, weights, dimension), case
        certificate = result['certificate']
        assert verify_weighted_orbit_certificate(size, pairs, weights, certificate,
                                                 dimension=dimension), case
        for key in stats:
            stats[key] += result['stats'][key]
        if case % 20 == 0:
            if certificate['histogram']:
                damaged = copy.deepcopy(certificate)
                damaged['histogram'][0]['weight'][0] += 1
                assert not verify_weighted_orbit_certificate(
                    size, pairs, weights, damaged, dimension=dimension)
                tamper_checks += 1
                damaged = copy.deepcopy(certificate)
                damaged['histogram'][0]['orbits'] += 1
                assert not verify_weighted_orbit_certificate(
                    size, pairs, weights, damaged, dimension=dimension)
                tamper_checks += 1
            if certificate['weights']:
                damaged = copy.deepcopy(certificate)
                damaged['weights'][0][2][0] += 1
                assert not verify_weighted_orbit_certificate(
                    size, pairs, weights, damaged, dimension=dimension)
                tamper_checks += 1
        if certificate['orbit_proof']['operations']:
            exemplar = size, pairs, weights, dimension, certificate

    # Huge integer data is checked algebraically; the literal oracle is not run here.
    huge = 2 ** 20000 + 29
    pairs = [IntervalPairing(0, huge - 1, huge, 2 * huge - 1)]
    weights = [(0, huge, (huge, -huge, 1)),
               (huge, 2 * huge, (-huge + 1, huge + 2, -1))]
    result = weighted_orbit_histogram(2 * huge, pairs, weights,
                                      record_certificate=True)
    assert result['histogram'] == [dict(weight=[1, 2, 0], orbits=huge)]
    certificate = json.loads(json.dumps(json_safe(result['certificate'])))
    assert verify_weighted_orbit_certificate(2 * huge, pairs, weights, certificate)

    # Replay must not call the weighted producer or its transport helpers.
    import fastunknot.weighted_orbits as producer
    old = (producer.weighted_orbit_histogram, producer._truncate_translation,
           producer._truncate_reflection, producer._replay)

    def fail(*args, **kwargs):
        raise AssertionError('independent checker called weighted producer')

    producer.weighted_orbit_histogram = producer._truncate_translation = fail
    producer._truncate_reflection = producer._replay = fail
    try:
        assert verify_weighted_orbit_certificate(2 * huge, pairs, weights, certificate)
        size, pairs, weights, dimension, certificate = exemplar
        assert verify_weighted_orbit_certificate(size, pairs, weights, certificate,
                                                 dimension=dimension)
    finally:
        (producer.weighted_orbit_histogram, producer._truncate_translation,
         producer._truncate_reflection, producer._replay) = old
    return dict(schema='independent-weighted-checker-audit-v1', seed=SEED,
                literal_cases=CASES, tamper_checks=tamper_checks,
                huge_endpoint_bits=(2 * huge).bit_length(), producer_disabled_checks=2,
                elapsed_seconds=time.perf_counter() - started, **stats, **source_metadata())


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path,
                        default=ROOT / 'results' / 'weighted_checker_audit_20261009.json',
                        help='destination JSON file, relative to the current directory if needed')
    args = parser.parse_args()
    result = run()
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
