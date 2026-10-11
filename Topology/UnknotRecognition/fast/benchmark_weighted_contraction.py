"""Paired static contraction and complete prism-query measurements."""
import argparse
from contextlib import contextmanager
from hashlib import sha256
import gc
import json
from pathlib import Path
import platform
import random
import statistics
import subprocess
from time import perf_counter
from types import ModuleType

from fastunknot import weighted_orbits
from fastunknot.integer_codec import json_safe
from fastunknot.normal_prism_interfaces import normal_prism_face_regions
from fastunknot.normal_prism_interfaces_verify import verify_normal_prism_interfaces
from normal_orbit_research.fixtures import layered_torus

BASELINE = '5a5c0ed6573d25fcabf93653d72449f76df2df79'
FAST = Path(__file__).resolve().parent
REPO = FAST.parents[2]
SOURCE = 'Topology/UnknotRecognition/fast/fastunknot/weighted_orbits.py'


@contextmanager
def contraction(function):
    original = weighted_orbits._contract_weights
    weighted_orbits._contract_weights = function
    try:
        yield
    finally:
        weighted_orbits._contract_weights = original


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    source = subprocess.check_output(['git', 'show', BASELINE + ':' + SOURCE], cwd=REPO)
    old = ModuleType('fastunknot.pinned_weighted_orbits')
    old.__package__ = 'fastunknot'
    exec(compile(source, BASELINE + ':' + SOURCE, 'exec'), old.__dict__)
    functions = {'sorted': old._contract_weights, 'sorted_control': old._contract_weights,
                 'sweep': weighted_orbits._contract_weights}
    cases, details = {}, {}
    for count in (1000, 10000, 100000):
        for pattern in ('many_gaps', 'no_gaps'):
            runs = [(i * 4, (i + 1) * 4, (i % 7, -i % 5, 1)) for i in range(count)]
            gaps = [(i * 4 + 1, i * 4 + 2) for i in range(count)] if pattern == 'many_gaps' else []
            name = f'local_{count}_{pattern}'
            cases[name] = ('local', runs, count * 4, gaps)
            details[name] = dict(scope='contraction only', runs=count, gaps=len(gaps), repetitions=3)
    for t in (4, 16, 32):
        raw, rows = layered_torus(t)
        cases[f'query_{t}'] = ('query', raw, rows)
        details[f'query_{t}'] = dict(scope='complete query, independent replay and JSON serialization',
                                    tetrahedra=t, repetitions=3)
    paths = [Path(__file__), FAST/'fastunknot/weighted_orbits.py',
             FAST/'fastunknot/weighted_orbit_verify.py', FAST/'fastunknot/interval_orbits.py',
             FAST/'fastunknot/normal_prism_interfaces.py', FAST/'fastunknot/normal_prism_interfaces_verify.py',
             FAST/'normal_orbit_research/fixtures.py']
    pins = {str(p.relative_to(REPO)): sha256(p.read_bytes()).hexdigest() for p in paths}

    def run(case, arm):
        if case[0] == 'local':
            _, runs, size, gaps = case
            histogram = {}
            answer, emitted = functions[arm](runs, size, gaps, histogram, lambda: None)
            return dict(runs=answer, histogram=sorted(histogram.items()), emitted=emitted)
        _, raw, rows = case
        with contraction(functions[arm]):
            answer = normal_prism_face_regions(raw, rows, record_certificate=True, port_encoding='vector')
            assert verify_normal_prism_interfaces(raw, rows, answer['certificate'])
            return json.dumps(json_safe(answer), sort_keys=True, separators=(',', ':'))

    rng = random.Random(26101102)
    samples, expected = [], {}
    for round_number in range(6):
        tasks = [(name, arm) for name in cases for arm in functions]
        rng.shuffle(tasks)
        for name, arm in tasks:
            repetitions = details[name]['repetitions']
            gc.collect()
            start = perf_counter()
            results = [run(cases[name], arm) for _ in range(repetitions)]
            elapsed = (perf_counter() - start) / repetitions
            digests = {sha256(json.dumps(json_safe(value), sort_keys=True,
                                        separators=(',', ':')).encode()).hexdigest() for value in results}
            assert len(digests) == 1
            digest = digests.pop()
            assert expected.setdefault(name, digest) == digest, (name, arm)
            samples.append(dict(case=name, arm=arm, round=round_number, warmup=round_number == 0,
                                seconds=elapsed, result_sha256=digest))
            # Release the preceding workload before the next arm's timer.
            # Otherwise a tiny case can inherit disposal of 100,000 runs.
            del results
        print('completed round', round_number, flush=True)
    for p in paths:
        assert sha256(p.read_bytes()).hexdigest() == pins[str(p.relative_to(REPO))]
    summary = {}
    for name in cases:
        rows = [r for r in samples if r['case'] == name and not r['warmup']]
        ratios = [next(r['seconds'] for r in rows if r['round'] == i and r['arm'] == 'sorted') /
                  next(r['seconds'] for r in rows if r['round'] == i and r['arm'] == 'sweep')
                  for i in range(1, 6)]
        controls = [next(r['seconds'] for r in rows if r['round'] == i and r['arm'] == 'sorted') /
                    next(r['seconds'] for r in rows if r['round'] == i and r['arm'] == 'sorted_control')
                    for i in range(1, 6)]
        summary[name] = dict(paired_sorted_over_sweep=statistics.median(ratios),
            paired_identical_control=statistics.median(controls),
            median_seconds={arm: statistics.median(r['seconds'] for r in rows if r['arm'] == arm)
                            for arm in functions})
    output = dict(baseline=BASELINE, baseline_source_sha256=sha256(source).hexdigest(),
                  python=platform.python_version(), seed=26101102, source_sha256=pins,
                  timing='Workload preparation, git loading and digest comparison excluded. Local cases '
                         'include fresh histogram allocation. Query cases include source preparation, '
                         'orbit discovery, weight transport, independent replay and JSON serialization. '
                         'Five shuffled paired rounds plus one warmup and an identical sorted control. '
                         'Query cases force vector port encoding in every arm. Prior results are released '
                         'and garbage is collected outside each timer. Not full recognizer timings.',
                  details=details, summary=summary, samples=samples)
    args.output.write_text(json.dumps(output, indent=2) + '\n')
    print(json.dumps(summary, indent=2))


if __name__ == '__main__':
    main()
