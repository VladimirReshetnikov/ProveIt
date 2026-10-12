"""Paired complete native-source queries, with proof replay timed separately.

No source geometry or orbit output is reused between timed calls.  Each call
starts with a triangulation and normal coordinates, includes source preparation,
geometry construction, discovery, complete cyclic assembly and certificate
creation.  The optional packet wrapper is deliberately not mixed into these
comparisons, since upstream base-profile proofs are an additional input.
"""

import argparse
from datetime import datetime, timezone
from functools import partial
import json
import platform
import statistics
import time
from pathlib import Path

from fastunknot.integer_codec import json_safe
from fastunknot.parallelity_boundary_words import normal_parallelity_boundary_words
from fastunknot.parallelity_boundary_words_verify import verify_parallelity_boundary_words
from normal_orbit_research.fixtures import layered_torus

from native_moments import normal_parallelity_moment_words, native_projection
from native_moments_verify import verify_native_moment_words


ROOT = Path(__file__).resolve().parents[1]


def benchmark(repeats=5):
    bank = json.loads((ROOT / 'code/native_moments_sources.json').read_text())['cases']
    cases = []
    for tetrahedra in (2, 4, 8, 16):
        raw, rows = layered_torus(tetrahedra)
        cases.append((f'layered-{tetrahedra}', raw, rows, 1))
    raw, rows = layered_torus(2)
    for bits in (32, 512, 16384):
        cases.append((f'binary-{bits}', raw, [[(1 << bits) * x for x in row] for row in rows], bits))
    for index, name in ((3, 'cap-only'), (145, 'port-free-binary')):
        item = bank[index]
        cases.append((name, item['triangulation'], item['coordinates'], None))
    output, examples = [], []
    producers = (normal_parallelity_boundary_words, normal_parallelity_moment_words,
                 partial(normal_parallelity_moment_words, codec='four'))
    checkers = (verify_parallelity_boundary_words, verify_native_moment_words, verify_native_moment_words)
    for name, raw, rows, bits in cases:
        # One untimed pass per implementation warms interpreter and reference
        # validation paths.  Timed calls still rebuild all source/query data.
        for producer, checker in zip(producers, checkers):
            warmup = producer(raw, rows, record_certificate=True)
            if warmup['status'] != 'COMPLETE' or not checker(raw, rows, warmup['certificate']):
                raise AssertionError('warmup proof failed')
        elapsed = [[], [], []]
        replay = [[], [], []]
        latest = [None, None, None]
        for iteration in range(repeats):
            for index in ((0, 1, 2) if iteration % 2 == 0 else (2, 1, 0)):
                start = time.perf_counter()
                answer = producers[index](raw, rows, record_certificate=True)
                elapsed[index].append(time.perf_counter() - start)
                if answer['status'] != 'COMPLETE':
                    raise AssertionError('unbounded native compiler did not finish')
                start = time.perf_counter()
                verified = checkers[index](raw, rows, answer['certificate'])
                replay[index].append(time.perf_counter() - start)
                if not verified:
                    raise AssertionError('native certificate failed independent replay')
                latest[index] = answer
            if native_projection(latest[1]['skeleton']) != latest[0]['skeleton']:
                raise AssertionError('complete cyclic interfaces differ')
            if latest[1]['skeleton'] != latest[2]['skeleton']:
                raise AssertionError('pair and four-field codecs disagree')
        def measurements(index):
            stats = latest[index]['stats']
            traces = [row for row in stats.values() if 'orbit_cycles' in row]
            result = dict(discovery_seconds=elapsed[index],
                          discovery_median=statistics.median(elapsed[index]),
                          replay_seconds=replay[index], replay_median=statistics.median(replay[index]),
                          weighted_calls=len(traces),
                          orbit_cycles=sum(row['orbit_cycles'] for row in traces),
                          maximum_weight_runs=max((row['maximum_weight_runs'] for row in traces), default=0),
                          certificate_bytes=len(json.dumps(json_safe(latest[index]['certificate']),
                                                           separators=(',', ':')).encode()))
            if index > 0:
                result['compilation'] = stats.get('compilation', {})
            return result
        old, new, four = measurements(0), measurements(1), measurements(2)
        row = dict(case=name, tetrahedra=len(raw['tetrahedra']), multiplicity_exponent=bits,
                   ports=len(latest[1]['skeleton']['ports']),
                   gap_lengths=[gap['unmarked_edges'] for gap in latest[1]['skeleton']['gaps']],
                   existing_native=old, moment_native=new,
                   four_field_native=four,
                   discovery_speedup=old['discovery_median'] / new['discovery_median'],
                   replay_speedup=old['replay_median'] / new['replay_median'],
                   codec_discovery_speedup=four['discovery_median'] / new['discovery_median'],
                   codec_replay_speedup=four['replay_median'] / new['replay_median'])
        output.append(row)
        if name in ('layered-4', 'binary-16384', 'cap-only'):
            examples.append(dict(case=name, triangulation=raw, coordinates=rows,
                                 certificate=latest[1]['certificate']))
        print(json.dumps({key: row[key] for key in ('case', 'ports', 'discovery_speedup', 'replay_speedup')}), flush=True)
    (ROOT / 'results/native_moments_certificates.json').write_text(
        json.dumps(json_safe(dict(source_commit='704600626606a9097cfd89d4e3d2bbc63c8dd1cb',
                                  fixtures=examples)), indent=2) + '\n')
    return dict(schema='native-moments-paired-full-query-benchmark-v1',
                source_commit='704600626606a9097cfd89d4e3d2bbc63c8dd1cb',
                python=platform.python_version(), platform=platform.platform(), repeats=repeats,
                utc_time=datetime.now(timezone.utc).isoformat(),
                warmup_calls_per_implementation_per_case=1,
                ordering='alternating existing-pair-four and four-pair-existing',
                scope='complete source-bound cyclic queries with certificates; replay separately; no knot recognizer timing',
                samples=output)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--repeats', type=int, default=5)
    parser.add_argument('--output', type=Path, default=ROOT / 'results/native_moments_benchmark.json')
    args = parser.parse_args()
    if args.repeats < 1:
        parser.error('repeats must be positive')
    result = benchmark(args.repeats)
    args.output.write_text(json.dumps(json_safe(result), indent=2) + '\n')


if __name__ == '__main__':
    main()
