"""Paired exact-source timings of full orbit counts and normal-surface queries."""

import argparse
from collections import defaultdict
import importlib.util
import json
from pathlib import Path
import platform
import random
import statistics
import sys
import time


def load_baseline(path):
    spec = importlib.util.spec_from_file_location('pinned_interval_orbits', path)
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--fast-dir', type=Path, required=True)
    parser.add_argument('--baseline', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--rounds', type=int, default=7)
    parser.add_argument('--seed', type=int, default=26100945)
    args = parser.parse_args()
    sys.path.insert(0, str(args.fast_dir.resolve()))
    from fastunknot.interval_orbits import IntervalPairing, count_orbits
    from fastunknot.interval_orbit_verify import verify_orbit_certificate
    from fastunknot.normal_surface_orbits import normal_arc_pairings, normal_surface_topology
    from fastunknot.normal_component_profile import normal_component_profile
    from normal_orbit_research.fixtures import layered_torus
    old = load_baseline(args.baseline)
    rng = random.Random(args.seed)
    cases = []

    for m in (8, 16, 32, 64, 128):
        period = 10*m
        rows = [(i, period+2*i-1, period+2*i, 2*period+3*i-1, False)
                for i in range(m)]
        rows += [(m, period+2*m-1, period+2*m, 2*period+3*m-1, False)] * m
        cases.append(dict(name=f'five-cycle-{m}', family='five-cycle', parameter=m,
                          n=23*m, rows=rows, expected_orbits=1))
    for count in (16, 64, 128, 256):
        cases.append(dict(name=f'easy-duplicates-{count}', family='easy-duplicates',
                          parameter=count, n=16,
                          rows=[(0, 7, 8, 15, False)]*count, expected_orbits=8))
    for t in (4, 8, 16, 32, 64, 96, 128):
        tri, coords = layered_torus(t)
        n, pairs = normal_arc_pairings(tri, coords)
        rows = [(p.a, p.b, p.c, p.d, p.reverse) for p in pairs]
        cases.append(dict(name=f'normal-meridian-{t}', family='normal-meridian',
                          parameter=t, n=n, rows=rows, expected_orbits=1))
    for bits in (64, 1024, 4096):
        m, period = 16, (1 << bits)+160
        rows = [(i, period+2*i-1, period+2*i, 2*period+3*i-1, False)
                for i in range(m)]
        rows += [(m, period+2*m-1, period+2*m, 2*period+3*m-1, False)] * m
        cases.append(dict(name=f'binary-size-{bits}', family='binary-size', parameter=bits,
                          n=2*period+3*m, rows=rows, expected_orbits=1))

    raw, summaries, certifications = [], [], []
    for case in cases:
        old_pairs = [old.IntervalPairing(*row) for row in case['rows']]
        new_pairs = [IntervalPairing(*row) for row in case['rows']]
        answers = {'baseline': old.count_orbits(case['n'], old_pairs, record_certificate=True)}
        for arm in ('adaptive', 'queue'):
            answers[arm] = count_orbits(case['n'], new_pairs, merger_scheduler=arm,
                                       record_certificate=True)
        reference = answers['baseline']
        assert reference.orbits == case['expected_orbits']
        for arm, answer in answers.items():
            assert answer.complete and answer.orbits == reference.orbits
            assert answer.cycles == reference.cycles
            assert answer.certificate == reference.certificate
            assert verify_orbit_certificate(case['n'], new_pairs, answer.certificate)
        certifications.append(dict(case=case['name'], exact_trace_equal=True,
                                   independently_verified=True, cycles=reference.cycles,
                                   orbits=reference.orbits))
        # Excluded untimed warm-up uses the complete workload once per arm.
        for arm in ('baseline', 'adaptive', 'queue'):
            if arm == 'baseline':
                old.count_orbits(case['n'], old_pairs)
            else:
                count_orbits(case['n'], new_pairs, merger_scheduler=arm)
        samples = defaultdict(list)
        paired = defaultdict(dict)
        for repeat in range(args.rounds):
            order = ['baseline', 'adaptive', 'queue']
            rng.shuffle(order)
            for arm in order:
                begin = time.perf_counter_ns()
                if arm == 'baseline':
                    answer = old.count_orbits(case['n'], old_pairs)
                else:
                    answer = count_orbits(case['n'], new_pairs, merger_scheduler=arm)
                elapsed = (time.perf_counter_ns()-begin)/1e9
                assert answer.complete and answer.orbits == reference.orbits
                samples[arm].append(elapsed)
                paired[repeat][arm] = elapsed
                raw.append(dict(case=case['name'], family=case['family'],
                                parameter=case['parameter'], round=repeat, arm=arm,
                                seconds=elapsed, pair_tests=answer.stats['pair_tests'],
                                cycles=answer.cycles, queue_switches=answer.stats.get(
                                    'merger_queue_switches', 0), peak_queue=answer.stats.get(
                                    'merger_peak_queue', 0)))
        summary = dict(name=case['name'], family=case['family'], parameter=case['parameter'],
                       pairings=len(new_pairs), universe_bits=case['n'].bit_length(),
                       cycles=reference.cycles,
                       medians={arm:statistics.median(values) for arm,values in samples.items()},
                       pair_tests={arm:answer.stats['pair_tests'] for arm,answer in answers.items()},
                       median_paired_speedup={arm:statistics.median(
                           row['baseline']/row[arm] for row in paired.values())
                           for arm in ('adaptive','queue')},
                       adaptive_queue_switches=answers['adaptive'].stats['merger_queue_switches'],
                       adaptive_peak_queue=answers['adaptive'].stats['merger_peak_queue'])
        summaries.append(summary)
        print(case['name'], 'adaptive paired speedup',
              round(summary['median_paired_speedup']['adaptive'], 3), flush=True)

    topology_raw, topology_summaries = [], []
    for t in (4, 16, 32, 64, 96):
        tri, coords = layered_torus(t)
        # Distinct outputs: these are costs of stronger information, not a
        # same-task speed ratio. Both include fresh geometry and input checks.
        methods = {'aggregate_topology': normal_surface_topology,
                   'component_profile': normal_component_profile}
        for method in methods.values():
            method(tri, coords)
        samples = defaultdict(list)
        for repeat in range(args.rounds):
            order = list(methods)
            rng.shuffle(order)
            for arm in order:
                begin = time.perf_counter_ns()
                answer = methods[arm](tri, coords)
                elapsed = (time.perf_counter_ns()-begin)/1e9
                assert answer['components'] == 1
                samples[arm].append(elapsed)
                topology_raw.append(dict(tetrahedra=t, arm=arm, round=repeat,
                                         seconds=elapsed, cycles=answer['cycles']))
        topology_summaries.append(dict(tetrahedra=t, medians={
            arm:statistics.median(values) for arm,values in samples.items()}))
        print('topology', t, topology_summaries[-1]['medians'], flush=True)

    result = dict(seed=args.seed, rounds=args.rounds,
                  baseline_commit='274909dd8724e411ece14e47ac4addea717aeca6',
                  python=sys.version, platform=platform.platform(),
                  scope='Full interval count on preconstructed immutable input; no certificate in timing',
                  topology_scope='Complete native geometry plus query; outputs differ, no speedup claim',
                  excluded_warmups=3*len(cases)+2*5,
                  certifications=certifications, samples=raw, summaries=summaries,
                  topology_samples=topology_raw, topology_summaries=topology_summaries)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2)+'\n')


if __name__ == '__main__':
    main()
