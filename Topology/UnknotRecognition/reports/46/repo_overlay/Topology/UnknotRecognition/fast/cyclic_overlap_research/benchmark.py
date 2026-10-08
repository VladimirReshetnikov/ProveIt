"""Paired whole-recognition and all-pairs cyclic-overlap audit.

Run from fast/: python -B cyclic_overlap_research/benchmark.py --output PATH
Inputs, raw timings, exclusions, certificates, and source hashes are retained.
The random presentation lists are kernel workloads, not hard-knot instances.
"""
import argparse
from hashlib import sha256
import json
from pathlib import Path
import platform
import random
from statistics import median
import subprocess
import sys
from time import perf_counter
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from fastunknot import Diagram, recognize
from fastunknot.group_certificate import _Budget, group_certificate, verify_group_certificate
from fastunknot.relator_overlap import overlap_move, pairwise_overlap_move
from benchmark_compressed_words import cases as hard_cases

BASELINE = '58ee11a97d5fd7f21647c57eefaf3ecc007931d6'
SEED = 261008903
ARMS = ('pairwise', 'control', 'adaptive', 'joint')
TRACKED = ('fastunknot/relator_overlap.py', 'fastunknot/cyclic_overlap_index.py',
    'fastunknot/group_certificate.py', 'fastunknot/compressed_search.py',
    'fastunknot/compressed_group.py', 'fastunknot/diagram.py', 'fastunknot/recognize.py',
    'benchmark_compressed_words.py', 'hard_unknots.py', 'normal_research/gordian.json',
    'cyclic_overlap_research/benchmark.py')


def digest(value):
    return sha256(json.dumps(value, sort_keys=True, separators=(',', ':')).encode()).hexdigest()


def sources():
    return {p: sha256((ROOT/p).read_bytes()).hexdigest() for p in TRACKED}


def cases():
    for name, d in hard_cases():
        yield name, d, 'UNKNOT'
    for name in ('trefoil', 'figure_eight', 'conway', 'kinoshita_terasaka'):
        d = Diagram.from_json(json.loads((ROOT/'examples'/(name+'.json')).read_text()))
        yield name, d, 'KNOTTED'


def stage_records(evidence):
    out = []
    for key, value in evidence.items():
        if key == 'group':
            out.append(value)
        elif isinstance(value, dict):
            out.extend(stage_records(value))
        elif isinstance(value, list):
            for item in value:
                if isinstance(item, dict):
                    out.extend(stage_records(item))
    return out


def summarize(samples):
    medians = {}
    for arm in ARMS:
        completed = [s['measurements'][arm]['seconds'] for s in samples
                     if s['measurements'][arm]['completed']]
        medians[arm] = median(completed) if completed else None
    ratios = {}
    for a, b in (('pairwise', 'control'), ('pairwise', 'adaptive'), ('pairwise', 'joint')):
        values = [s['measurements'][a]['seconds']/s['measurements'][b]['seconds']
                  for s in samples if s['measurements'][a]['completed']
                  and s['measurements'][b]['completed']]
        ratios[a+'/'+b] = dict(count=len(values), median=median(values) if values else None)
    return dict(completed_median_seconds=medians, paired_ratios=ratios)


def full_queries(rounds, rng):
    rows, certificates = [], {}
    modes = {'explicit': dict(use_group=True, group_relators=True, group_seconds=10,
                group_max_work=20_000_000, seconds=12, max_objects=50_000),
             'compressed': dict(use_group=True, group_relators=True, group_seconds=10,
                group_max_work=20_000_000, group_compressed_search=True,
                seconds=12, max_objects=50_000)}
    for name, diagram, expected in cases():
        row = dict(name=name, crossings=diagram.crossings, pd=diagram.pd,
                   input_sha256=digest(diagram.pd), expected=expected, modes={})
        for mode, options in modes.items():
            samples, warmups = [], []
            for repetition in range(rounds+1):
                order = list(ARMS)
                rng.shuffle(order)
                measurements = {}
                for arm in order:
                    queries = []
                    backend = 'pairwise' if arm == 'control' else arm
                    def query(words, budget):
                        stats = {}
                        answer = overlap_move(words, budget, backend=backend, stats=stats)
                        queries.append(stats)
                        return answer
                    with patch('fastunknot.relator_overlap.overlap_move', query):
                        start = perf_counter()
                        result = recognize(Diagram.from_pd(diagram.pd), **options)
                        elapsed = perf_counter()-start
                    completed = result.status in ('UNKNOT', 'KNOTTED')
                    if completed:
                        assert result.status == expected, (name, mode, arm, result)
                    groups = []
                    for group in stage_records(result.evidence):
                        record = {k:v for k,v in group.items() if k != 'certificate'}
                        if 'certificate' in group:
                            key = digest(group['certificate'])
                            certificates[key] = group['certificate']
                            record['certificate_sha256'] = key
                        groups.append(record)
                    measurements[arm] = dict(seconds=elapsed, status=result.status,
                        method=result.method, completed=completed, overlap_queries=queries,
                        group_stages=groups, reason=result.evidence.get('reason'))
                sample = dict(order=order, measurements=measurements)
                (samples if repetition else warmups).append(sample)
            result = dict(warmups=warmups, samples=samples, **summarize(samples))
            row['modes'][mode] = result
            print('whole', name, mode, result['completed_median_seconds'], flush=True)
        rows.append(row)
    return rows, certificates, modes


def captured_gordian():
    diagram = Diagram.from_json(json.loads((ROOT/'normal_research/gordian.json').read_text()))
    snapshots = []
    def capture(words, budget):
        snapshots.append([list(word) for word in words])
        return pairwise_overlap_move(words, budget)
    with patch('fastunknot.relator_overlap.overlap_move', capture):
        certificate = group_certificate(diagram, relator_moves=True, max_work=20_000_000)
    assert verify_group_certificate(diagram, certificate, max_work=20_000_000)
    assert len(snapshots) == 1
    return snapshots[0]


def kernels(rounds, rng):
    data_rng = random.Random(SEED+1)
    lists = [('gordian-derived', captured_gordian(), 'actual residual presentation')]
    for count, length in ((8, 64), (32, 64), (128, 64)):
        words = [data_rng.choices((-4,-3,-2,-1,1,2,3,4),k=length)
                 for _ in range(count)]
        lists.append((f'random-{count}x{length}', words, 'synthetic exact-query capacity'))
    lists.append(('duplicate-periodic', [[1,2,3,4]*256 for _ in range(32)],
                  'synthetic highly periodic early bound'))
    rows = []
    for name, words, provenance in lists:
        expected = pairwise_overlap_move(words, _Budget(lambda:None, 10**9, 10**9))
        expected_gain = 0 if expected is None else 2*expected['overlap']-len(words[expected['donor']])
        samples, warmups = [], []
        for repetition in range(rounds+1):
            order = list(ARMS)
            rng.shuffle(order)
            measurements = {}
            for arm in order:
                backend = 'pairwise' if arm == 'control' else arm
                budget, stats = _Budget(lambda:None,10**9,10**9), {}
                start = perf_counter()
                move = overlap_move(words, budget, backend=backend, stats=stats)
                elapsed = perf_counter()-start
                gain = 0 if move is None else 2*move['overlap']-len(words[move['donor']])
                assert gain == expected_gain, (name, backend, gain, expected_gain)
                measurements[arm] = dict(seconds=elapsed, completed=True, status='EXACT',
                    gain=gain, move=move, work=10**9-budget.left, stats=stats)
            sample = dict(order=order, measurements=measurements)
            (samples if repetition else warmups).append(sample)
        result = dict(name=name, provenance=provenance, words=words,
            input_sha256=digest(words), total_length=sum(map(len,words)),
            nonempty_relators=sum(bool(w) for w in words), expected_gain=expected_gain,
            warmups=warmups, samples=samples, **summarize(samples))
        rows.append(result)
        print('kernel', name, result['completed_median_seconds'], flush=True)
    return rows


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--rounds', type=int, default=5)
    parser.add_argument('--kernel-rounds', type=int, default=3)
    args = parser.parse_args()
    if min(args.rounds,args.kernel_rounds) < 1:
        parser.error('round counts must be positive')
    frozen, rng = sources(), random.Random(SEED)
    raw = subprocess.check_output(['git','show',BASELINE+
        ':Topology/UnknotRecognition/fast/fastunknot/relator_overlap.py'],cwd=ROOT)
    rows, certificates, configurations = full_queries(args.rounds,rng)
    kernel_rows = kernels(args.kernel_rounds,rng)
    assert sources() == frozen, 'measured source changed during run'
    data = dict(baseline=BASELINE, baseline_overlap_source_sha256=sha256(raw).hexdigest(),
        source_sha256=frozen, measured_sources_unchanged=True,
        python=sys.version, platform=platform.platform(), seed=SEED,
        whole_measured_rounds=args.rounds, kernel_measured_rounds=args.kernel_rounds,
        excluded_warmups_per_case_mode_arm=1, configurations=configurations,
        query_scope='fresh PD validation plus all recognition stages and independent certificate replay',
        kernel_scope='existing explicit relators; include index construction, failed prelude and exact search; exclude input generation',
        import_scope='all imports and corpus construction excluded consistently; no persistence or file output timed',
        censoring='UNKNOWN/INCONCLUSIVE retained and excluded from completed medians/pairs',
        caveat='synthetic presentation lists do not demonstrate hard-knot recognition; joint-only regressions retained',
        rows=rows, kernels=kernel_rows, certificates=certificates)
    args.output.parent.mkdir(parents=True,exist_ok=True)
    args.output.write_text(json.dumps(data,indent=2)+'\n')


if __name__ == '__main__':
    main()
