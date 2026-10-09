"""Paired benchmarks for repeated certified interval-component membership.

All timed arms receive an already constructed interval system.  The compiled
arm includes discovery, independent verification, compilation and all queries.
This is a repeated supplied-relation benchmark, not a knot recognition test.
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

HERE = Path(__file__).resolve().parent
UPSTREAM = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(UPSTREAM))

from fastunknot.interval_orbits import IntervalPairing, count_orbits, same_orbit
from fastunknot.integer_codec import json_safe
from fastunknot.normal_surface_geometry import normal_arc_pairings
from normal_orbit_research.fixtures import layered_torus, interior_vertex_torus
from fastunknot.orbit_index import prepare_orbit_index


def source_manifest():
    files = [UPSTREAM / 'fastunknot' / 'orbit_index.py', HERE / 'benchmark.py',
             UPSTREAM / 'tests' / 'test_orbit_index.py']
    files += [UPSTREAM / 'fastunknot' / filename for filename in
              ('interval_orbits.py', 'interval_orbit_verify.py', 'integer_codec.py',
               'normal_surface_geometry.py')]
    files += [UPSTREAM / 'normal_orbit_research' / 'fixtures.py']
    return {str(path.relative_to(UPSTREAM)):
            hashlib.sha256(path.read_bytes()).hexdigest() for path in files}


def cases():
    output = []
    for tetrahedra, scale, counts in ((8, (1 << 512) + 1, (1, 8, 32)),
                                     (24, (1 << 128) + 1, (1, 8, 32)),
                                     (8, 1, (32,))):
        raw, vector = layered_torus(tetrahedra)
        scaled = [[scale * entry for entry in row] for row in vector]
        size, pairs = normal_arc_pairings(raw, scaled)
        for queries in counts:
            output.append(dict(name=f'layered_{tetrahedra}_scale_{scale.bit_length()}bit_q{queries}',
                               size=size, pairings=pairs, queries=queries,
                               topology='parallel meridian discs',
                               tetrahedra=tetrahedra, coordinate_scale=scale))
    raw, _ = layered_torus(1)
    scale = (1 << 1024) + 1
    size, pairs = normal_arc_pairings(raw, [[0, 0, 0, 0, 0, scale, 0]])
    output.append(dict(name='mobius_1025bit_q32', size=size, pairings=pairs, queries=32,
                       topology='odd multiple of a one-sided Mobius band',
                       tetrahedra=1, coordinate_scale=scale))
    raw, basis = interior_vertex_torus()
    coefficients = [(1 << 256) + 1, (1 << 257) + 7, (1 << 258) + 9]
    vector = [[sum(a * values[j] for a, values in zip(coefficients,
                         (basis['sphere'][i], basis['boundary_disk'][i], basis['mobius'][i])))
               for j in range(7)] for i in range(4)]
    size, pairs = normal_arc_pairings(raw, vector)
    output.append(dict(name='mixed_native_4_q32', size=size, pairings=pairs, queries=32,
                       topology='sphere, boundary disc and one-sided band mixture',
                       tetrahedra=4))
    period = (1 << 1024) + 3
    pairs = [IntervalPairing(i * period, (i + 1) * period - 1,
                             (i + 1) * period, (i + 2) * period - 1)
             for i in range(64)]
    output.append(dict(name='periodic_chain_64_q32', size=65 * period,
                       pairings=pairs, queries=32, topology='abstract interval relation'))
    return output


def make_queries(case, rng):
    size, pairs, requested = case['size'], case['pairings'], case['queries']
    samples = []
    while len(samples) < requested:
        if len(samples) % 2 == 0 and pairs:
            pairing = rng.choice(pairs)
            first = pairing.a + rng.randrange(pairing.b - pairing.a + 1)
            second = (pairing.a + pairing.d - first if pairing.reverse
                      else first + pairing.c - pairing.a)
        else:
            first, second = rng.randrange(size), rng.randrange(size)
        if first != second:
            samples.append((first, second))
    return samples


def legacy(size, pairs, samples):
    return [same_orbit(size, pairs, first, second) for first, second in samples]


def shared(size, pairs, samples):
    # This stronger baseline shares the original count, and uses exact connected
    # or wholly static shortcuts. It still discovers each augmented relation.
    result = count_orbits(size, pairs)
    if result.orbits == 1:
        return [True] * len(samples)
    if result.orbits == size:
        return [first == second for first, second in samples]
    answer = []
    for first, second in samples:
        if first == second:
            answer.append(True)
        else:
            augmented = pairs + [IntervalPairing(first, first, second, second)]
            answer.append(count_orbits(size, augmented).orbits == result.orbits)
    return answer


def compiled(size, pairs, samples):
    index, _ = prepare_orbit_index(size, pairs)
    return [index.same_orbit(first, second) for first, second in samples]


def run(output, rounds):
    rng = random.Random(202610090742)
    manifest = source_manifest()
    result = dict(schema='compiled-orbit-index-benchmark-v1', seed=202610090742,
                  python=sys.version, platform=platform.platform(), rounds=rounds,
                  warmup_rounds=1, source_manifest_before=manifest, cases=[])
    arms = dict(legacy=legacy, shared=shared, shared_control=shared,
                compiled=compiled, compiled_control=compiled)
    for case in cases():
        samples = make_queries(case, rng)
        size, pairs = case['size'], case['pairings']
        expected = shared(size, pairs, samples)
        index, proof_result = prepare_orbit_index(size, pairs)
        locations = [index.locate(point) for sample in samples for point in sample]
        batch = 3 if case['queries'] == 1 else 1
        records = []
        for round_index in range(rounds + 1):
            order = list(arms)
            rng.shuffle(order)
            elapsed = {}
            for arm in order:
                start = time.perf_counter_ns()
                answers = [arms[arm](size, pairs, samples) for _ in range(batch)]
                duration = (time.perf_counter_ns() - start) / (1e9 * batch)
                if any(answer != expected for answer in answers):
                    raise AssertionError((case['name'], arm, 'different answers'))
                elapsed[arm] = duration
            records.append(dict(round=round_index, warmup=round_index == 0,
                                order=order, seconds=elapsed))
        measured = [record['seconds'] for record in records if not record['warmup']]
        median_times = {arm: statistics.median(record[arm] for record in measured)
                        for arm in arms}
        paired = {label: statistics.median(record[left] / record[right]
                                           for record in measured)
                  for label, left, right in (
                      ('legacy_over_compiled', 'legacy', 'compiled'),
                      ('shared_over_compiled', 'shared', 'compiled'),
                      ('shared_control', 'shared', 'shared_control'),
                      ('compiled_control', 'compiled', 'compiled_control'))}
        details = {key: value for key, value in case.items() if key != 'pairings'}
        details.update(pairings=[[p.a, p.b, p.c, p.d, -1 if p.reverse else 1]
                                 for p in pairs], samples=samples, answers=expected,
                       batch=batch, pairing_count=len(pairs), universe_bits=size.bit_length(),
                       orbit_count=index.count, index_statistics=index.statistics,
                       count_cycles=proof_result.cycles,
                       point_forward_steps=sum(location.forward_steps for location in locations),
                       point_reverse_contractions=sum(location.reverse_contractions for location in locations),
                       minimum_representatives=[location.representative for location in locations],
                       records=records, median_seconds=median_times, paired_ratios=paired)
        result['cases'].append(details)
        print(case['name'], json.dumps(dict(median_seconds=median_times, paired_ratios=paired)), flush=True)
    after = source_manifest()
    if manifest != after:
        raise AssertionError('a pinned benchmark source changed during execution')
    result['source_manifest_after'] = after
    output.write_text(json.dumps(json_safe(result), indent=2) + '\n')
    return result


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--output', type=Path, default=UPSTREAM / 'results' / 'orbit_index.json')
    parser.add_argument('--rounds', type=int, default=7)
    args = parser.parse_args()
    if args.rounds < 3:
        parser.error('use at least three measured rounds')
    run(args.output, args.rounds)
