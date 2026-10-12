#!/usr/bin/env python3
"""Paired native source queries and complete certified AHT replay comparisons.

The native comparison uses two isolated Python processes and a temporary
baseline package whose changed verifier is restored from the pinned Git
object.  No public or private module bindings are monkeypatched.  Timed native
work includes source reconstruction, certificate production, independent
whole-cut replay when complete, and exact JSON serialization.  Corpus parsing
and Python process startup are outside the timed interval.
"""

import argparse
import hashlib
import json
import os
from pathlib import Path
import platform
import shutil
import statistics
import subprocess
import sys
import tempfile
import time

PIN = 'e0b2f802f336fcb51e9ec5f29174cfe28dfb9d39'
VERIFY = 'Topology/UnknotRecognition/fast/fastunknot/weighted_orbit_verify.py'


def worker(args):
    """Fresh source preparation, production, public replay, and JSON serialization."""
    sys.path.insert(0, str(Path(args.fast).resolve()))
    from fastunknot.integer_codec import json_safe
    from fastunknot.normal_cut_handlebodies import normal_cut_handlebodies
    from fastunknot.normal_cut_handlebodies_verify import verify_normal_cut_handlebodies
    cases = {case['id']: case for case in json.loads(Path(args.cases).read_text())}
    for line in sys.stdin:
        command = json.loads(line)
        case = cases[command['id']]
        begin = time.perf_counter()
        answer = normal_cut_handlebodies(case['triangulation'], case['coordinates'],
                                         record_certificate=True,
                                         boundary_method=case['boundary_method'])
        generated = time.perf_counter()
        accepted = None
        if answer['status'] == 'COMPLETE':
            accepted = verify_normal_cut_handlebodies(case['triangulation'], case['coordinates'],
                                                       answer['certificate'])
            if not accepted:
                raise AssertionError('whole-cut certificate rejected')
        replayed = time.perf_counter()
        payload = json.dumps(json_safe(answer), sort_keys=True, separators=(',', ':')).encode()
        finished = time.perf_counter()
        print(json.dumps(dict(id=case['id'], status=answer['status'], accepted=accepted,
                              production_seconds=generated - begin,
                              replay_seconds=replayed - generated,
                              serialization_seconds=finished - replayed,
                              total_seconds=finished - begin,
                              result_sha256=hashlib.sha256(payload).hexdigest(),
                              serialized_bytes=len(payload))), flush=True)


def send(process, case):
    process.stdin.write(json.dumps({'id': case}) + '\n')
    process.stdin.flush()
    line = process.stdout.readline()
    if not line:
        raise RuntimeError('benchmark worker exited before returning its result')
    return json.loads(line)


def native(args, output):
    repo = Path(args.repo).resolve()
    fast = repo / 'Topology/UnknotRecognition/fast'
    sys.path.insert(0, str(fast))
    from normal_orbit_research.fixtures import layered_torus
    bank_path = fast / 'marked_parallelity_research/corpus.json'
    bank = json.loads(bank_path.read_text())['cases']
    chosen = ['pilot/lst_4_7/0', 'pilot/finite_trefoil/0', 'pilot/solid_torus_sum_rp3/0',
              'interior_1_2/mixed', 'fibonacci_lst_09/mixed', 'finite_trefoil/mixed']
    cases = []
    for name in chosen:
        case = next(case for case in bank if case['id'] == name)
        cases.append(dict(id=name + ':moments', triangulation=case['triangulation'],
                          coordinates=case['coordinates'], boundary_method='moments'))
    for name in ('pilot/lst_4_7/0', 'interior_1_2/mixed'):
        case = next(case for case in bank if case['id'] == name)
        cases.append(dict(id=name + ':masks', triangulation=case['triangulation'],
                          coordinates=case['coordinates'], boundary_method='masks'))
    for size in (4, 8, 16):
        raw, rows = layered_torus(size)
        cases.append(dict(id=f'layered_meridian_{size}_scale3:moments', triangulation=raw,
                          coordinates=[[3 * value for value in row] for row in rows],
                          boundary_method='moments'))
    case_path = output.with_name('native_cases.json')
    case_path.write_text(json.dumps(cases, indent=2) + '\n')
    original = subprocess.check_output(['git', 'show', f'{args.pin}:{VERIFY}'], cwd=repo)
    current = (repo / VERIFY).read_bytes()
    result = dict(pin=args.pin, python=sys.version, platform=platform.platform(), rounds=args.rounds,
                  corpus_sha256=hashlib.sha256(bank_path.read_bytes()).hexdigest(),
                  original_verifier_sha256=hashlib.sha256(original).hexdigest(),
                  current_verifier_sha256=hashlib.sha256(current).hexdigest(),
                  cases_sha256=hashlib.sha256(case_path.read_bytes()).hexdigest(),
                  timing_contract=worker.__doc__, cases=[])
    with tempfile.TemporaryDirectory(prefix='proveit-flat-replay-') as temp:
        baseline = Path(temp)
        shutil.copytree(fast / 'fastunknot', baseline / 'fastunknot',
                        ignore=shutil.ignore_patterns('__pycache__'))
        (baseline / 'fastunknot/weighted_orbit_verify.py').write_bytes(original)
        processes = {}
        try:
            for name, source in (('flat', baseline), ('lazy', fast)):
                processes[name] = subprocess.Popen(
                    [sys.executable, '-u', __file__, '--worker', '--fast', str(source),
                     '--cases', str(case_path)], stdin=subprocess.PIPE,
                    stdout=subprocess.PIPE, text=True)
            for index, case in enumerate(cases):
                # One complete untimed warmup for each backend and source.
                for process in processes.values():
                    send(process, case['id'])
                samples = {key: [] for key in processes}
                for round_id in range(args.rounds):
                    order = ('flat', 'lazy') if (index + round_id) % 2 == 0 else ('lazy', 'flat')
                    for name in order:
                        samples[name].append(send(processes[name], case['id']))
                hashes = {item['result_sha256'] for rows in samples.values() for item in rows}
                if len(hashes) != 1:
                    raise AssertionError(f'complete result changed for {case["id"]}')
                medians = {name: {field: statistics.median(row[field] for row in rows)
                                  for field in ('production_seconds', 'replay_seconds',
                                                'serialization_seconds', 'total_seconds')}
                           for name, rows in samples.items()}
                record = dict(id=case['id'], tetrahedra=len(case['coordinates']),
                              status=samples['flat'][0]['status'], samples=samples,
                              medians=medians,
                              full_query_speedup=medians['flat']['total_seconds'] /
                                                 medians['lazy']['total_seconds'])
                if record['status'] == 'COMPLETE':
                    record['replay_speedup'] = (medians['flat']['replay_seconds'] /
                                                medians['lazy']['replay_seconds'])
                result['cases'].append(record)
                output.write_text(json.dumps(result, indent=2) + '\n')
                print(case['id'], record['status'], 'full', round(record['full_query_speedup'], 3),
                      'replay', round(record.get('replay_speedup', 0), 3), flush=True)
        finally:
            for process in processes.values():
                process.stdin.close()
                process.wait()
    result['sum_case_medians'] = {
        name: {field: sum(row['medians'][name][field] for row in result['cases'])
               for field in ('production_seconds', 'replay_seconds',
                             'serialization_seconds', 'total_seconds')}
        for name in ('flat', 'lazy')}
    output.write_text(json.dumps(result, indent=2) + '\n')


def synthetic(args, output):
    fast = Path(args.repo).resolve() / 'Topology/UnknotRecognition/fast'
    sys.path.insert(0, str(fast))
    from fastunknot.interval_orbits import IntervalPairing
    from fastunknot.weighted_orbits import weighted_orbit_histogram
    from fastunknot.weighted_orbit_verify import (
        _canonical_pairings, _initial_weights, _replay_local,
        verify_weighted_orbit_certificate, verify_weighted_orbit_certificate_reference)
    rows = []
    for steps in (16, 32, 64, 128):
        width = steps * steps
        size = (steps + 1) * width
        pairs = [IntervalPairing(0, width - 1, j * width, (j + 1) * width - 1)
                 for j in range(1, steps + 1)]
        weights = [(i, i + 1, [i % 2]) for i in range(width)]
        weights.append((width, size, [1]))
        begin = time.perf_counter()
        produced = weighted_orbit_histogram(size, pairs, weights, record_certificate=True)
        generation = time.perf_counter() - begin
        proof = produced['certificate']
        expected = [dict(weight=[steps], orbits=width // 2),
                    dict(weight=[steps + 1], orbits=width // 2)]
        if produced['histogram'] != expected:
            raise AssertionError('stress family histogram differs')
        functions = dict(flat=verify_weighted_orbit_certificate_reference,
                         lazy=verify_weighted_orbit_certificate)
        for function in functions.values():
            if not function(size, pairs, weights, proof):
                raise AssertionError('stress family warmup rejected')
        samples = {name: [] for name in functions}
        for round_id in range(args.rounds):
            order = ('flat', 'lazy') if round_id % 2 == 0 else ('lazy', 'flat')
            for name in order:
                begin = time.perf_counter()
                accepted = functions[name](size, pairs, weights, proof)
                elapsed = time.perf_counter() - begin
                if not accepted:
                    raise AssertionError('stress family timed replay rejected')
                samples[name].append(elapsed)
        dimension, runs = _initial_weights(size, weights, 1, lambda: None)
        metrics = {}
        _replay_local(size, _canonical_pairings(size, pairs), runs,
                       proof['orbit_proof']['operations'], dimension, lambda: None, metrics)
        operations = {}
        for event in proof['orbit_proof']['operations']:
            operations[event['op']] = operations.get(event['op'], 0) + 1
        record = dict(steps=steps, width=width, represented_points=size,
                      proof_operations=operations, generation_seconds=generation,
                      samples=samples, medians={key: statistics.median(value)
                                              for key, value in samples.items()},
                      metrics=metrics, histogram=expected)
        record['speedup'] = record['medians']['flat'] / record['medians']['lazy']
        rows.append(record)
        output.write_text(json.dumps(dict(python=sys.version, platform=platform.platform(),
                                         rounds=args.rounds, cases=rows), indent=2) + '\n')
        print('AHT', steps, width, round(record['speedup'], 3), 'times', flush=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--repo', default='/workspace/scratch/621c73e1194a/ProveIt')
    parser.add_argument('--pin', default=PIN)
    parser.add_argument('--rounds', type=int, default=3)
    parser.add_argument('--output', type=Path)
    parser.add_argument('--synthetic', action='store_true')
    parser.add_argument('--worker', action='store_true')
    parser.add_argument('--fast')
    parser.add_argument('--cases')
    args = parser.parse_args()
    if args.worker:
        worker(args)
    else:
        if args.output is None or args.rounds < 1:
            parser.error('--output and positive --rounds are required')
        args.output.parent.mkdir(parents=True, exist_ok=True)
        (synthetic if args.synthetic else native)(args, args.output.resolve())


if __name__ == '__main__':
    main()
