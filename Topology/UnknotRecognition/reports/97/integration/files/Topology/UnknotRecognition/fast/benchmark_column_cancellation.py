"""Paired raw cancellation and genuine source-cut benchmarks.

Run from fast/: python benchmark_column_cancellation.py --output RESULTS.json
The two baseline modules are exact files from the pinned source commit.
Synthetic matrices measure one kernel; they are not knot inputs. The real
106-case corpus measures prepared cores and complete supplied-cut queries.
"""

import argparse
from collections import Counter
from datetime import datetime, timezone
from hashlib import sha256
import importlib
import importlib.util
import json
from pathlib import Path
import platform
from statistics import median
from time import perf_counter

from fastunknot.column_cancellation_verify import verify_column_cancellations
from fastunknot.core_handlebody import column_cancellation_plan, core_handlebody_certificate
from fastunknot.core_handlebody_verify import verify_core_handlebody_certificate
from fastunknot.normal_cut_handlebodies_verify import verify_normal_cut_handlebodies
from fastunknot.normal_parallelity_geometry import _parallelity_geometry
from fastunknot.normal_surface_geometry import _prepare, _coordinates


ROOT = Path(__file__).resolve().parent
BASELINE = '704600626606a9097cfd89d4e3d2bbc63c8dd1cb'


def load_baseline(filename, module_name):
    path = ROOT / 'column_cancellation_research' / filename
    spec = importlib.util.spec_from_file_location(module_name, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def timed(function, repeats):
    started = perf_counter()
    for _ in range(repeats):
        function()
    return (perf_counter() - started) / repeats


def paired(before, after, trials=5, target_seconds=0.02):
    probe = [timed(before, 1), timed(after, 1)]
    repeats = [max(1, min(256, int(target_seconds / max(value, 1e-9))))
               for value in probe]
    samples = [[], []]
    functions = [before, after]
    for trial in range(trials):
        for index in ((0, 1) if trial % 2 == 0 else (1, 0)):
            samples[index].append(timed(functions[index], repeats[index]))
    centers = list(map(median, samples))
    return dict(before_seconds=samples[0], after_seconds=samples[1],
                before_median_seconds=centers[0], after_median_seconds=centers[1],
                before_over_after=centers[0] / centers[1],
                repeats=repeats, trials=trials)


def synthetic_core(size):
    """Incidence-only cyclic words; not an authenticated embedded 3D input."""
    return dict(handles0=[dict(id=0)],
                handles1=[dict(id=c, ends=[0, 0]) for c in range(size + 1)],
                handles2=[dict(id=r, cycle=[dict(dimension=0, handle=0),
                                              dict(dimension=1, handle=r),
                                              dict(dimension=0, handle=0),
                                              dict(dimension=1, handle=r + 1)])
                          for r in range(size)], handles3=[])


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--output', type=Path,
                        default=ROOT / 'results/column_cancellation_20261012.json')
    parser.add_argument('--trials', type=int, default=5)
    parser.add_argument('--skip-whole-cuts', action='store_true')
    args = parser.parse_args()
    old = load_baseline('baseline_core_handlebody.py', 'column_baseline_core')
    old_verify = load_baseline('baseline_core_handlebody_verify.py',
                               'fastunknot.column_baseline_verify')
    output = dict(baseline_commit=BASELINE,
                  generated_utc=datetime.now(timezone.utc).isoformat(),
                  environment=dict(python=platform.python_version(),
                                   implementation=platform.python_implementation(),
                                   platform=platform.platform()),
                  scope='raw positive-singleton core cancellation; no knot decision gain',
                  synthetic_producer=[], synthetic_replay=[])

    for size in (16, 64, 256, 1024, 4096):
        counts = {r: {r: 1, r + 1: 1} for r in range(size)}
        a, b = old.capped_cancellation_plan(counts), column_cancellation_plan(counts)
        assert not a['remaining_rows'] and not b['remaining_rows']
        assert verify_column_cancellations(counts, b['cancellations'])
        record = dict(rows=size, columns=size + 1, nonzeros=2 * size,
                      before_stats=a['stats'], after_stats=b['stats'])
        record.update(paired(lambda: old.capped_cancellation_plan(counts),
                             lambda: column_cancellation_plan(counts), args.trials))
        output['synthetic_producer'].append(record)
        print('producer', size, record['before_over_after'], flush=True)

    for size in (16, 32, 64, 128, 256):
        core = synthetic_core(size)
        result = core_handlebody_certificate(core)
        new_proof = result['certificate']
        old_proof = dict(new_proof, schema='normal-core-handlebody-v1', method='capped')
        assert old_verify.verify_core_handlebody_certificate(core, old_proof)
        assert verify_core_handlebody_certificate(core, new_proof)
        record = dict(rows=size, columns=size + 1,
                      scope='conditional core replay on synthetic incidence words')
        record.update(paired(
            lambda: old_verify.verify_core_handlebody_certificate(core, old_proof),
            lambda: verify_core_handlebody_certificate(core, new_proof), args.trials))
        output['synthetic_replay'].append(record)
        print('replay', size, record['before_over_after'], flush=True)

    corpus_path = ROOT / 'marked_parallelity_research/corpus.json'
    cases = json.loads(corpus_path.read_text())['cases']
    output['corpus_sha256'] = sha256(corpus_path.read_bytes()).hexdigest()
    cores, source_records = [], []
    for case in cases:
        prepared = _prepare(case['triangulation'], lambda: None)
        vector = _coordinates(prepared, case['coordinates'], lambda: None)
        core = _parallelity_geometry(prepared, vector, lambda: None)['core']
        a, b = old.core_handlebody_certificate(core), core_handlebody_certificate(core)
        assert a['status'] == b['status']
        if a['status'] == 'COMPLETE':
            assert [c['genus'] for c in a['components']] == [c['genus'] for c in b['components']]
            assert old_verify.verify_core_handlebody_certificate(core, a['certificate'])
            assert verify_core_handlebody_certificate(core, b['certificate'])
        source_records.append(dict(id=case['id'], status=b['status'],
                                   method=b.get('certificate', {}).get('method'),
                                   reason=b.get('reason')))
        cores.append((core, a, b))
    output['source_cases'] = source_records
    output['source_summary'] = dict(Counter(r['method'] or r['reason'] for r in source_records))
    output['source_core_producer_all_106'] = paired(
        lambda: [old.core_handlebody_certificate(c) for c, _, _ in cores],
        lambda: [core_handlebody_certificate(c) for c, _, _ in cores], args.trials)
    column = [(c, a, b) for c, a, b in cores
              if b.get('certificate', {}).get('method') == 'column_leaf']
    output['source_core_producer_column_24'] = paired(
        lambda: [old.core_handlebody_certificate(c) for c, _, _ in column],
        lambda: [core_handlebody_certificate(c) for c, _, _ in column], args.trials)
    complete = [(c, a, b) for c, a, b in cores if b['status'] == 'COMPLETE']
    output['source_core_replay_complete_90'] = paired(
        lambda: [old_verify.verify_core_handlebody_certificate(c, a['certificate'])
                 for c, a, _ in complete],
        lambda: [verify_core_handlebody_certificate(c, b['certificate'])
                 for c, _, b in complete], args.trials)
    print('source core producer all 106',
          output['source_core_producer_all_106']['before_over_after'], flush=True)
    print('source core replay complete 90',
          output['source_core_replay_complete_90']['before_over_after'], flush=True)

    if not args.skip_whole_cuts:
        cut_module = importlib.import_module('fastunknot.normal_cut_handlebodies')
        current = cut_module.core_handlebody_certificate

        def whole(legacy=False):
            cut_module.core_handlebody_certificate = old.core_handlebody_certificate if legacy else current
            try:
                return [cut_module.normal_cut_handlebodies(
                    c['triangulation'], c['coordinates'], record_certificate=True) for c in cases]
            finally:
                cut_module.core_handlebody_certificate = current

        a, b = whole(True), whole(False)
        outcome = Counter()
        proofs = 0
        for case, left, right in zip(cases, a, b):
            assert left['status'] == right['status'], case['id']
            assert left.get('census') == right.get('census'), case['id']
            outcome[right['status']] += 1
            if right['status'] == 'COMPLETE':
                for result in (left, right):
                    assert verify_normal_cut_handlebodies(
                        case['triangulation'], case['coordinates'], result['certificate'])
                    proofs += 1
        output['whole_cut_validation'] = dict(outcomes=outcome, independently_replayed=proofs)
        output['whole_cut_producer_all_106'] = paired(
            lambda: whole(True), lambda: whole(False), args.trials, target_seconds=0.0)
        print('whole-cut producer all 106',
              output['whole_cut_producer_all_106']['before_over_after'], flush=True)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(output, indent=2) + '\n')
    print(args.output, flush=True)


if __name__ == '__main__':
    main()
