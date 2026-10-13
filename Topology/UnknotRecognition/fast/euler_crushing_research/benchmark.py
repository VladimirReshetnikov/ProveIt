"""Four complete positive-query arms with pinned sequential-driver provenance.

Run from fast/: python -B -m euler_crushing_research.benchmark --output PATH
Regina is not imported. Timings include exterior construction, shelling, native
replay, discovery and full-result serialization. Only diagram objects, imports,
the pinned historical driver and a separately verified warmup are prepared
outside the timed batches. Every timed output must match the warmup hash.
"""
import argparse
from hashlib import sha256
import json
from pathlib import Path
import platform
from random import Random
from statistics import median
import subprocess
import sys
from time import perf_counter_ns
from types import ModuleType

from fastunknot.diagram import Diagram
from fastunknot.diagram_exterior_verify import verify_diagram_exterior
from fastunknot.boundary_shellings_verify import verify_boundary_shellings
from fastunknot.normal_sector_verify import verify_sector_witness
from fastunknot.normal_crushing_search import recognize_by_crushing, verify_crushing_recognition
from fastunknot.normal_crushing_chain import verify_crushing_chain
from normal_crushing_research.benchmark import fixed_source_disc_query


ROOT = Path(__file__).resolve().parents[2]
BASELINE_COMMIT = '4ba20551b9314be0b8dff2c74c6e1e1793d9ce4a'
BASELINE_PATH = 'Topology/UnknotRecognition/fast/fastunknot/normal_crushing_search.py'
BASELINE_SHA256 = '2292da7fe9fe161ce0c605257ba4b960d3d4d5d54ae544d3b5c8fe177bda869b'
SEED = 11820261012
ARMS = ('adaptive_disc', 'prior_sequential', 'fair_corners', 'fair_lp')


def load_baseline():
    """Compile exactly the pinned driver with maintained shared dependencies."""
    raw = subprocess.run(['git', 'show', f'{BASELINE_COMMIT}:{BASELINE_PATH}'],
                         cwd=ROOT, check=True, capture_output=True).stdout
    if sha256(raw).hexdigest() != BASELINE_SHA256:
        raise AssertionError('historical sequential driver does not match its source pin')
    module = ModuleType('fastunknot._euler_benchmark_prior_crushing')
    module.__package__ = 'fastunknot'
    module.__file__ = f'git:{BASELINE_COMMIT}:{BASELINE_PATH}'
    exec(compile(raw, module.__file__, 'exec'), module.__dict__)
    return module


def baseline_pin():
    return dict(commit=BASELINE_COMMIT, path=BASELINE_PATH, sha256=BASELINE_SHA256,
                scope='historical sequential driver only; shared dependencies use the pinned current files')


def source_hashes():
    """Pin the entire native package and both research harnesses, without Regina."""
    paths = list((ROOT/'fast/fastunknot').rglob('*.py'))
    for name in ('euler_crushing_research', 'normal_crushing_research'):
        directory = ROOT/'fast'/name
        paths.extend(directory.glob('*.py'))
        if (directory/'README.md').exists():
            paths.append(directory/'README.md')
    return {str(path.relative_to(ROOT)): sha256(path.read_bytes()).hexdigest()
            for path in sorted(set(paths))}


def arm_configs(*, bounded=False):
    common = dict(max_sectors=64 if bounded else None,
                  max_bases=10000 if bounded else None, max_crushes=None,
                  sector_order='diversified')
    fair = dict(common, sector_quantum=64)
    return dict(adaptive_disc=dict(adaptive=True), prior_sequential=common,
                fair_corners=dict(fair, sector_method='corners'),
                fair_lp=dict(fair, sector_method='lp', lp_strategy='envelope',
                             max_pivots=1000 if bounded else 10000,
                             max_anchors=4096 if bounded else 10000))


def run_query(diagram, arm, baseline, config, *, check=lambda: None):
    if arm == 'adaptive_disc':
        return fixed_source_disc_query(diagram, **config)
    producer = baseline.recognize_by_crushing if arm == 'prior_sequential' else recognize_by_crushing
    return producer(diagram, check=check, **config)


def verify_result(diagram, result, arm):
    """Independent harness replay; callers choose whether it is timed."""
    if result['status'] == 'INCONCLUSIVE':
        if arm == 'adaptive_disc' or not verify_crushing_chain(diagram, result['partial_chain']):
            raise AssertionError('partial crushing chain failed independent replay')
        return 'partial_chain'
    if result['status'] not in ('UNKNOT', 'KNOTTED'):
        raise AssertionError('no conclusive recognition result to replay')
    proof = result['certificate']
    if arm == 'adaptive_disc':
        source, shelling = proof['source_triangulation'], proof['shelling']
        if (result['status'] != 'UNKNOT' or proof['input_pd'] != [list(row) for row in diagram.pd]
                or not verify_diagram_exterior(diagram, source)
                or not verify_boundary_shellings(source, shelling['triangulation'], shelling['moves'])
                or not verify_sector_witness(shelling['triangulation'], proof['disc'])):
            raise AssertionError('adaptive disc certificate failed independent replay')
    elif not verify_crushing_recognition(diagram, proof):
        raise AssertionError('recognition certificate failed independent replay')
    return 'recognition'


def encode_result(result):
    return json.dumps(result, sort_keys=True, separators=(',', ':')).encode()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', required=True)
    parser.add_argument('--pairs', type=int, default=9)
    parser.add_argument('--aa', type=int, default=3)
    parser.add_argument('--batch', type=int, default=3)
    args = parser.parse_args()
    if min(args.pairs, args.aa, args.batch) < 1:
        parser.error('pairs, aa and batch must be positive')
    baseline = load_baseline()
    configs = arm_configs()
    cases = [('circle', Diagram.from_pd([])), ('negative_curl', Diagram.from_braid(2, [-1]))]
    rng = Random(SEED)
    output = dict(passed=False, source_sha256=source_hashes(), baseline=baseline_pin(),
        pairs=args.pairs, aa=args.aa, batch=args.batch, seed=SEED, python=sys.version,
        platform=platform.platform(), arms=ARMS, configs=configs,
        scope='two complete positive queries; adaptive disc is the principal baseline; all arms include native construction, replay, search and serialization',
        validation='warmup outputs are independently replayed outside timing; every timed full-output hash must match its verified warmup',
        records=[])
    target = Path(args.output)

    def save():
        target.write_text(json.dumps(output, indent=2)+'\n')

    def query(diagram, arm):
        result = run_query(diagram, arm, baseline, configs[arm])
        if result['status'] != 'UNKNOT':
            raise AssertionError((arm, result))
        encoded = encode_result(result)
        return result, len(encoded), sha256(encoded).hexdigest()

    def sample(diagram, arm, expected):
        start = perf_counter_ns()
        for _ in range(args.batch):
            result, size, digest = query(diagram, arm)
            if digest != expected:
                raise AssertionError('timed full output differs from independently verified warmup')
        elapsed = perf_counter_ns()-start
        return dict(ns=elapsed/args.batch, stats=result['stats'], result_bytes=size,
                    output_sha256=digest)

    for name, diagram in cases:
        record = dict(id=name, input_pd=[list(row) for row in diagram.pd],
                      warmup_results={}, warmup_sha256={}, samples=[], aa_samples=[])
        for arm in ARMS:
            result, _, digest = query(diagram, arm)
            record['warmup_results'][arm] = result
            record['warmup_sha256'][arm] = digest
            if verify_result(diagram, result, arm) != 'recognition':
                raise AssertionError('warmup failed to prove recognition')
        for _ in range(args.pairs):
            order = list(ARMS); rng.shuffle(order)
            values = {arm: sample(diagram, arm, record['warmup_sha256'][arm]) for arm in order}
            record['samples'].append(dict(order=order, results=values))
        for _ in range(args.aa):
            order = ['A', 'B']; rng.shuffle(order)
            values = {label: sample(diagram, 'adaptive_disc', record['warmup_sha256']['adaptive_disc'])
                      for label in order}
            record['aa_samples'].append(dict(order=order, results=values))
        record['median_ns'] = {arm: median(p['results'][arm]['ns'] for p in record['samples'])
                               for arm in ARMS}
        record['paired_ratio'] = {f'{left}_over_{right}': median(
            p['results'][left]['ns']/p['results'][right]['ns'] for p in record['samples'])
            for left, right in (('adaptive_disc', 'fair_corners'), ('adaptive_disc', 'fair_lp'),
                                ('prior_sequential', 'fair_corners'), ('prior_sequential', 'fair_lp'),
                                ('fair_corners', 'fair_lp'))}
        record['aa_ratio'] = median(p['results']['A']['ns']/p['results']['B']['ns']
                                    for p in record['aa_samples'])
        output['records'].append(record)
        save()
        print(name, record['median_ns'], record['paired_ratio'], flush=True)
    if output['source_sha256'] != source_hashes():
        raise AssertionError('benchmarked source changed during the run')
    output['passed'] = True
    save()


if __name__ == '__main__':
    main()
