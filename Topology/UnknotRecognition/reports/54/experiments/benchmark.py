"""Controlled algebra-kernel benchmarks, NOT whole-knot recognition timings.
SPDX-License-Identifier: MIT-0
"""
import argparse
import hashlib
import json
import platform
import random
import statistics
import sys
import time
from pathlib import Path
ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from compiled_ports import Profiles, QuotientEngine, ConeProgram
from compiled_ports.profiles import json_safe
from compiled_ports.verify import verify_threshold, verify_change_points


def bisect_threshold(program, table, target):
    trials = 0
    if table.orbit_count <= target:
        return dict(index=0, trials=trials)
    if program.evaluate(table).count > target:
        return dict(index=None, trials=1)
    lo, hi, trials = 0, program.length, 1
    while lo + 1 < hi:
        mid = (lo + hi) // 2
        trials += 1
        if program.evaluate(table, mid).count <= target:
            hi = mid
        else:
            lo = mid
    return dict(index=hi, trials=trials)


def measured_arms(arms, rounds, rng, expected, repeats=None):
    repeats = repeats or {name: 1 for name in arms}
    samples = {name: [] for name in arms}
    outputs = {}
    for fn in arms.values():
        out = fn()
        assert expected(out)
    for round_index in range(rounds):
        names = list(arms)
        rng.shuffle(names)
        for name in names:
            before = time.perf_counter_ns()
            for _ in range(repeats[name]):
                answer = arms[name]()
            elapsed = time.perf_counter_ns() - before
            assert expected(answer)
            samples[name].append(dict(round=round_index, nanoseconds=elapsed/repeats[name],
                                      batch_nanoseconds=elapsed, repeats=repeats[name]))
            outputs[name] = answer
    return dict(samples=samples, last_outputs=outputs,
                median_ns={name: statistics.median(x['nanoseconds'] for x in values)
                           for name, values in samples.items()})


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, default=ROOT/'results'/'benchmarks.json')
    parser.add_argument('--rounds', type=int, default=7)
    args = parser.parse_args()
    if args.rounds < 1:
        parser.error('--rounds must be positive')
    rng = random.Random(261008640)
    output = dict(schema='compiled-port-benchmarks-v1', seed=261008640,
                  python=sys.version, platform=platform.platform(), rounds=args.rounds,
                  scope='Abstract encoded equivalence relations; no knot instances; '
                        'no native AHT benchmark; program construction is outside timed queries.',
                  threshold=[], height=[])
    table = Profiles.from_histogram(((1 << 256),)*8, {(1,)*8: 1 << 256})
    for b in (64, 256, 1024, 4096):
        delay = 1 << b
        records = [dict(op='cone', atoms=[]), dict(op='power', child=0, exponent=delay),
                   dict(op='cone', atoms=[3]), dict(op='concat', left=1, right=2),
                   dict(op='power', child=3, exponent=delay)]
        p = ConeProgram(8, records)
        answer = p.first_at_most(table, 1)
        assert verify_threshold(table, records, p.root, 1, answer['index'])
        arms = {'descent': lambda: p.first_at_most(table, 1),
                'descent_control': lambda: p.first_at_most(table, 1),
                'prefix_bisection': lambda: bisect_threshold(p, table, 1)}
        row = measured_arms(arms, args.rounds, rng, lambda a: a['index'] == delay + 1,
                            repeats={'descent': 1000, 'descent_control': 1000,
                                     'prefix_bisection': max(1, 1024//b)})
        row.update(exponent_bits=b+1, delay_exponent=b, grammar_nodes=len(records),
                   expanded_length_bits=p.length.bit_length(), atoms=8, profiles=1)
        output['threshold'].append(row)
    for m in (1, 4, 8, 16):
        table = Profiles.from_histogram((2,)*m,
            {tuple(int(j == i) for j in range(m)): 2 for i in range(m)})
        delay = 1 << 2048
        records = [dict(op='cone', atoms=[]), dict(op='power', child=0, exponent=delay)]
        root = 1
        groups = [[j] for j in range(m)] + [[0, j] for j in range(1, m)]
        for group in groups:
            records.append(dict(op='cone', atoms=group))
            leaf = len(records)-1
            records.append(dict(op='concat', left=root, right=leaf))
            root = len(records)-1
            records.append(dict(op='concat', left=root, right=1))
            root = len(records)-1
        records.append(dict(op='power', child=root, exponent=1 << 4096))
        p = ConeProgram(m, records)
        answer = p.change_points(table)
        assert verify_change_points(table, records, p.root, answer['events'])
        row = measured_arms({'events': lambda: p.change_points(table),
                             'events_control': lambda: p.change_points(table)},
                            args.rounds, rng,
                            lambda a: len(a['events']) == 2*m-1 and a['count'] == 1,
                            repeats={'events': max(10, 500//(m*m)),
                                     'events_control': max(10, 500//(m*m))})
        row.update(atoms=m, profiles=m, grammar_nodes=len(records),
                   expanded_length_bits=p.length.bit_length(), sharp_event_bound=2*m-1)
        output['height'].append(row)
    files = sorted((ROOT/'compiled_ports').glob('*.py')) + [Path(__file__)]
    output['source_sha256'] = {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest()
                               for p in files}
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(json_safe(output), indent=2)+'\n')
    for row in output['threshold']:
        print('threshold', row['delay_exponent'], 'trials',
              {k: v['trials'] for k, v in row['last_outputs'].items()},
              'median ms', {k: round(v/1e6, 6) for k, v in row['median_ns'].items()})
    for row in output['height']:
        print('events', row['atoms'], row['sharp_event_bound'],
              'trials', row['last_outputs']['events']['trials'],
              'median ms', round(row['median_ns']['events']/1e6, 6))

if __name__ == '__main__':
    main()
