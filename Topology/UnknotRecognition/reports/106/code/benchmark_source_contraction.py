"""Exact source-corpus comparison of source reuse and gap-prefix replay.

Run against a ProveIt checkout after applying the accompanying patches:
 python benchmark_source_contraction.py --repo /path/ProveIt --output results.json

The baseline is reconstructed with git archive at the declared source pin.
The two implementations use separate module namespaces in the same process.
Every source decision, census, statistic and certificate must agree exactly.
Randomized method order is paired within each case and repetition. Timings are
native producer plus independent native checker, not stand-alone knot verdicts.
"""
import argparse
from collections import Counter
import hashlib
import importlib
import io
import json
from pathlib import Path
import platform
import random
import shutil
import statistics
import subprocess
import sys
import tarfile
import tempfile
import time
import types

PIN = 'c6d0ec8aa0b6308310ab6c081ba29d8bc363ede5'
GAP_FILES = ('interval_orbits.py', 'interval_orbit_verify.py',
             'weighted_orbit_verify.py', 'weighted_transversal_verify.py')


def namespace(name, directory):
    package = types.ModuleType(name)
    package.__path__ = [str(directory)]
    package.__package__ = name
    sys.modules[name] = package
    produce = importlib.import_module(name + '.normal_cut_handlebodies').normal_cut_handlebodies
    replay = importlib.import_module(name + '.normal_cut_handlebodies_verify').verify_normal_cut_handlebodies
    return produce, replay


def sample(api, case):
    produce, replay = api
    start = time.perf_counter_ns()
    result = produce(case['triangulation'], case['coordinates'], record_certificate=True)
    middle = time.perf_counter_ns()
    if result['status'] == 'COMPLETE':
        assert replay(case['triangulation'], case['coordinates'], result['certificate'])
    end = time.perf_counter_ns()
    return result, {'produce': (middle-start)/1e9, 'replay': (end-middle)/1e9,
                    'total': (end-start)/1e9}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--repo', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--rounds', type=int, default=5)
    parser.add_argument('--ablation', action='store_true')
    parser.add_argument('--limit', type=int)
    parser.add_argument('--seed', type=int, default=20261012)
    args = parser.parse_args()
    if args.rounds < 1:
        parser.error('--rounds must be positive')
    runtime = args.repo/'Topology/UnknotRecognition/fast'
    corpus_bytes = (runtime/'marked_parallelity_research/corpus.json').read_bytes()
    corpus = json.loads(corpus_bytes)['cases']
    if args.limit is not None:
        corpus = corpus[:args.limit]
    report = dict(source_pin=PIN, corpus_sha256=hashlib.sha256(corpus_bytes).hexdigest(),
        python=sys.version, platform=platform.platform(), seed=args.seed, rounds=args.rounds,
        clock='perf_counter_ns', meaning='native whole-cut producer + independent native checker',
        baseline='exact pinned git archive', final_source_sha256={}, cases=[])
    for path in sorted((runtime/'fastunknot').rglob('*.py')):
        report['final_source_sha256'][str(path.relative_to(runtime/'fastunknot'))] = hashlib.sha256(path.read_bytes()).hexdigest()
    args.output.parent.mkdir(parents=True, exist_ok=True)
    with tempfile.TemporaryDirectory(prefix='unknot-prefix-bench-') as temporary:
        root = Path(temporary)
        archive = subprocess.check_output(['git', 'archive', PIN + ':Topology/UnknotRecognition/fast/fastunknot'], cwd=args.repo)
        (root/'baseline').mkdir()
        with tarfile.open(fileobj=io.BytesIO(archive)) as f:
            f.extractall(root/'baseline', filter='data')
        shutil.copytree(runtime/'fastunknot', root/'final', ignore=shutil.ignore_patterns('__pycache__'))
        variants = ['baseline']
        if args.ablation:
            shutil.copytree(root/'final', root/'source_reuse')
            for filename in GAP_FILES:
                shutil.copy2(root/'baseline'/filename, root/'source_reuse'/filename)
            variants.append('source_reuse')
        variants.append('final')
        apis = {name: namespace('bench_' + name, root/name) for name in variants}
        report['variants'] = variants
        rng = random.Random(args.seed)
        counts = Counter()
        total_start = time.perf_counter()
        for index, case in enumerate(corpus):
            baseline, warm = sample(apis['baseline'], case)
            for name in variants[1:]:
                value, warm = sample(apis[name], case)
                assert value == baseline, (case['id'], name, 'output differs')
            entry = dict(id=case['id'], tetrahedra=len(case['coordinates']),
                         status=baseline['status'], reason=baseline.get('reason'),
                         exact_output_parity=True, samples=[])
            counts[baseline['status']] += 1
            for repetition in range(args.rounds):
                order = variants.copy()
                rng.shuffle(order)
                record = dict(order=order)
                for name in order:
                    value, timing = sample(apis[name], case)
                    assert value == baseline, (case['id'], name, repetition)
                    record[name] = timing
                entry['samples'].append(record)
            entry['median_seconds'] = {name: {phase: statistics.median(
                s[name][phase] for s in entry['samples']) for phase in ('produce', 'replay', 'total')}
                for name in variants}
            entry['median_paired_ratios'] = {name: {phase: statistics.median(
                s['baseline'][phase]/s[name][phase] for s in entry['samples'])
                for phase in ('produce','replay','total') if phase != 'replay' or entry['status']=='COMPLETE'}
                for name in variants[1:]}
            report['cases'].append(entry)
            report.update(counts=counts, elapsed_seconds=time.perf_counter()-total_start)
            args.output.write_text(json.dumps(report, indent=2)+'\n')
            if (index+1)%10==0 or index+1==len(corpus):
                print(json.dumps(dict(done=index+1,total=len(corpus),counts=counts)),flush=True)
        report['aggregate'] = {}
        for name in variants:
            report['aggregate'][name] = {phase: sum(c['median_seconds'][name][phase]
                for c in report['cases']) for phase in ('produce','replay','total')}
        report['aggregate_ratios'] = {name: {phase: report['aggregate']['baseline'][phase]/report['aggregate'][name][phase]
            for phase in ('produce','replay','total')} for name in variants[1:]}
        report['median_case_paired_ratios'] = {name: {phase: statistics.median(c['median_paired_ratios'][name][phase]
            for c in report['cases'] if phase in c['median_paired_ratios'][name])
            for phase in ('produce','replay','total')} for name in variants[1:]}
        args.output.write_text(json.dumps(report, indent=2)+'\n')
        print(json.dumps({k:report[k] for k in ('counts','aggregate','aggregate_ratios','median_case_paired_ratios','elapsed_seconds')},indent=2))


if __name__=='__main__':
    main()
