"""Paired end-to-end query and certificate timings; no Regina dependency.

Run only after other research jobs have stopped. Each observation times the
complete public producer, including validation. New replay is timed separately.
Selection is based on fixture, polarity and structural dimensions, never timing.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import platform
import random
import statistics
import sys
from time import perf_counter_ns

ROOT = Path(__file__).resolve().parents[1]
FAST = ROOT / 'code' / 'fast'
if not FAST.exists():
    FAST = ROOT / 'work' / 'fast'
if not FAST.exists():
    FAST = ROOT / 'fast'
sys.path[:0] = [str(FAST), str(ROOT / 'scripts')]

from fibonacci_fixture import fibonacci_torus
from audit_sector_euler import old_screen
from fastunknot.integer_codec import json_safe
from fastunknot.normal_euler import decide_sector_euler
from fastunknot.normal_euler_verify import verify_sector_euler_certificate
from fastunknot.normal_ray import certify_normal_ray_disc
from fastunknot.normal_ray_verify import verify_normal_ray_disc
from fastunknot.normal_disk_kernel import (
    normal_compressing_disk_count, verify_normal_disk_count_certificate,
)


def timed(function):
    start = perf_counter_ns()
    answer = function()
    return answer, (perf_counter_ns() - start) / 1e9


def summary(values):
    return dict(median=statistics.median(values), minimum=min(values),
                maximum=max(values), observations=values)


def nbytes(certificate):
    return len(json.dumps(json_safe(certificate), sort_keys=True,
                          separators=(',', ':')).encode())


def environment():
    cpu = 'unavailable'
    info = Path('/proc/cpuinfo')
    if info.exists():
        for line in info.read_text().splitlines():
            if line.startswith('model name'):
                cpu = line.split(':', 1)[1].strip()
                break
    return dict(python=sys.version, platform=platform.platform(), cpu=cpu,
                logical_cpus=os.cpu_count(), timer='perf_counter_ns',
                cpu_affinity=sorted(os.sched_getaffinity(0)) if hasattr(os, 'sched_getaffinity') else None)


def sector_benchmark(repeats, rng):
    audit = json.loads((ROOT/'results/sector_euler_audit.json').read_text())
    corpus = json.loads((ROOT/'results/discovery_corpus.json').read_text())
    fixtures = {r['id']: r for r in corpus['records']}
    names = ['fibonacci_lst_10', 'cap_3_5_3', 'finite_trefoil',
             'finite_trefoil_interior', 'finite_figureEight',
             'finite_figureEight_interior', 'solid_torus_sum_rp3',
             'solid_torus_sum_s2xs1']
    selection = []
    for name in names:
        if name not in fixtures:
            raise ValueError('Missing predeclared fixture '+name)
        for positive in (False, True):
            candidates = [r for r in audit['records'] if r['fixture_id'] == name
                          and r['expected_q_positive'] == positive]
            candidates.sort(key=lambda r: (-r['new_stats']['matching_nullity'],
                -r['new_stats']['active_vertices'], -len(r['support']), r['support']))
            if candidates:
                selection.append(candidates[0])
    output = []
    for selected in selection:
        raw = fixtures[selected['fixture_id']]['triangulation']
        support = selected['support']
        expected = 'POSITIVE_EULER' if selected['expected_q_positive'] else 'NO_POSITIVE_EULER'
        calls = {
            'old': lambda: old_screen(raw, support, None),
            'old_copy': lambda: old_screen(raw, support, None),
            'anchors': lambda: decide_sector_euler(raw, support),
            'envelope': lambda: decide_sector_euler(raw, support, strategy='envelope'),
        }
        # One untimed warm-up for every implementation and checker.
        for name, function in calls.items():
            answer = function()
            assert answer['status'] == expected
            if 'certificate' in answer:
                assert verify_sector_euler_certificate(raw, answer['certificate'])
        samples = {name: [] for name in calls}
        replay = {name: [] for name in ('anchors', 'envelope')}
        latest = {}
        order = []
        for _ in range(repeats):
            names_order = list(calls)
            rng.shuffle(names_order)
            order.append(names_order)
            for name in names_order:
                answer, seconds = timed(calls[name])
                assert answer['status'] == expected
                samples[name].append(seconds)
                latest[name] = answer
                if name in replay:
                    okay, elapsed = timed(lambda: verify_sector_euler_certificate(raw, answer['certificate']))
                    assert okay
                    replay[name].append(elapsed)
        record = dict(fixture_id=selected['fixture_id'], tetrahedra=selected['tetrahedra'],
            support=support, status=expected, matching_nullity=selected['new_stats']['matching_nullity'],
            active_vertices=selected['new_stats']['active_vertices'],
            anchors_total=selected['new_stats']['anchors_total'], order=order,
            producer_seconds={name: summary(values) for name, values in samples.items()},
            replay_seconds={name: summary(values) for name, values in replay.items()},
            stats={name: answer['stats'] for name, answer in latest.items()},
            certificate_bytes={name: nbytes(latest[name]['certificate']) for name in replay})
        output.append(record)
        print('sector', record['fixture_id'], expected, 'd='+str(record['matching_nullity']), flush=True)
    return output


def ray_benchmark(repeats, rng):
    output = []
    for t in (4, 8, 16, 32, 64, 128):
        fixture = fibonacci_torus(t)
        raw, rows = fixture['triangulation'], fixture['coordinates']
        calls = {
            'old': lambda: normal_compressing_disk_count(raw, rows, record_certificate=True),
            'old_copy': lambda: normal_compressing_disk_count(raw, rows, record_certificate=True),
            'ray': lambda: certify_normal_ray_disc(raw, rows),
        }
        verifiers = {'old': verify_normal_disk_count_certificate,
                     'old_copy': verify_normal_disk_count_certificate,
                     'ray': verify_normal_ray_disc}
        for name, function in calls.items():
            answer = function()
            assert answer['status'] == ('DISC_FOUND' if name == 'ray' else 'COMPLETE')
            if name != 'ray':
                assert answer['compressing_disk_components'] == 1
            assert verifiers[name](raw, rows, answer['certificate'])
        producer = {name: [] for name in calls}
        replay = {name: [] for name in calls}
        latest, order = {}, []
        for _ in range(repeats):
            current = list(calls)
            rng.shuffle(current)
            order.append(current)
            for name in current:
                answer, seconds = timed(calls[name])
                okay, elapsed = timed(lambda: verifiers[name](raw, rows, answer['certificate']))
                assert okay
                producer[name].append(seconds)
                replay[name].append(elapsed)
                latest[name] = answer
        record = dict(tetrahedra=t, maximum_coordinate_bits=fixture['maximum_coordinate'].bit_length(),
            normal_disc_count=str(fixture['normal_disc_count']), order=order,
            producer_seconds={name: summary(values) for name, values in producer.items()},
            replay_seconds={name: summary(values) for name, values in replay.items()},
            combined_seconds={name: summary([a+b for a,b in zip(producer[name], replay[name])]) for name in calls},
            certificate_bytes={name: nbytes(answer['certificate']) for name, answer in latest.items()},
            stats={name: answer['stats'] for name, answer in latest.items()})
        output.append(record)
        print('ray paired', t, flush=True)
    scaling = []
    for t in (256, 512, 1024):
        fixture = fibonacci_torus(t)
        raw, rows = fixture['triangulation'], fixture['coordinates']
        answer = certify_normal_ray_disc(raw, rows)
        assert verify_normal_ray_disc(raw, rows, answer['certificate'])
        producer, replay = [], []
        for _ in range(repeats):
            answer, seconds = timed(lambda: certify_normal_ray_disc(raw, rows))
            okay, elapsed = timed(lambda: verify_normal_ray_disc(raw, rows, answer['certificate']))
            assert answer['status'] == 'DISC_FOUND' and okay
            producer.append(seconds)
            replay.append(elapsed)
        scaling.append(dict(tetrahedra=t,
            maximum_coordinate_bits=fixture['maximum_coordinate'].bit_length(),
            normal_disc_count=str(fixture['normal_disc_count']),
            producer_seconds=summary(producer), replay_seconds=summary(replay),
            combined_seconds=summary([a+b for a,b in zip(producer,replay)]),
            certificate_bytes=nbytes(answer['certificate']), stats=answer['stats']))
        print('ray scaling', t, flush=True)
    return output, scaling


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--repeats', type=int, default=5)
    parser.add_argument('--seed', type=int, default=20261009)
    parser.add_argument('--output', type=Path, default=ROOT/'results/controlled_benchmarks.json')
    args = parser.parse_args()
    if args.repeats < 1:
        parser.error('repeats must be positive')
    rng = random.Random(args.seed)
    result = dict(schema='dual-continuation-controlled-benchmarks-v1',
        environment=environment(), repeats=args.repeats, seed=args.seed,
        isolation='Run after all other task research/audit/test jobs finished; shared host scheduling remains uncontrolled.',
        scope='Full producer and independent replay separately; no input construction, JSON serialization, file I/O or oracle enumeration inside timed region.',
        selection='Predeclared fixture/polarity strata; highest nullity, then active vertices, then support size, then lexicographic support. No time-based selection.',
        source_sha256={p.name: hashlib.sha256(p.read_bytes()).hexdigest() for p in
            [Path(__file__), FAST/'fastunknot/normal_euler.py', FAST/'fastunknot/exact_lp.py',
             FAST/'fastunknot/normal_ray.py', FAST/'fastunknot/normal_ray_verify.py',
             FAST/'fastunknot/normal_disk_kernel.py']})
    result['sectors'] = sector_benchmark(args.repeats, rng)
    args.output.write_text(json.dumps(json_safe(result), indent=2)+'\n')
    result['ray_paired'], result['ray_scaling'] = ray_benchmark(args.repeats, rng)
    args.output.write_text(json.dumps(json_safe(result), indent=2)+'\n')
    print(args.output, flush=True)


if __name__ == '__main__':
    main()
