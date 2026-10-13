"""Paired complete positive queries with flat sectors and certified Euler trees."""
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
from fastunknot.normal_crushing_search import recognize_by_crushing
from euler_crushing_research.benchmark import (
    ROOT, encode_result, verify_result)
from normal_crushing_research.benchmark import fixed_source_disc_query
from vertex_reduction_research.benchmark import source_hashes as previous_hashes

BASELINE_COMMIT = '6c2fd5aae'
BASELINE_PATH = 'Topology/UnknotRecognition/fast/fastunknot/normal_crushing_search.py'
BASELINE_SHA256 = '6f73ff897fea86b0ed59d45f11be3eb0e68484a99b1f7aefc1b24c3714713472'
ARMS = ('adaptive_disc', 'prior_vertex_q', 'prior_vertex_lp', 'tree_restricted', 'tree_source')
SEED = 12020261012


def source_hashes():
    result = previous_hashes()
    fixture = ROOT/'fast/normal_orbit_research/fixtures.py'
    result[str(fixture.relative_to(ROOT))] = sha256(fixture.read_bytes()).hexdigest()
    for path in sorted((ROOT/'fast/euler_tree_research').iterdir()):
        if path.suffix in ('.py', '.md'):
            result[str(path.relative_to(ROOT))] = sha256(path.read_bytes()).hexdigest()
    return dict(sorted(result.items()))


def baseline_pin():
    return dict(commit=BASELINE_COMMIT, path=BASELINE_PATH, sha256=BASELINE_SHA256,
        scope='historical vertex-preprocessed flat-sector driver only; shared dependencies use current pinned sources')


def load_baseline():
    raw = subprocess.run(['git', 'show', f'{BASELINE_COMMIT}:{BASELINE_PATH}'],
                         cwd=ROOT, check=True, capture_output=True).stdout
    assert sha256(raw).hexdigest() == BASELINE_SHA256
    module = ModuleType('fastunknot._tree_benchmark_prior_crushing')
    module.__package__ = 'fastunknot'
    module.__file__ = f'git:{BASELINE_COMMIT}:{BASELINE_PATH}'
    exec(compile(raw, module.__file__, 'exec'), module.__dict__)
    return module


def arm_configs(*, bounded=False):
    common = dict(max_sectors=64 if bounded else None,
                  max_bases=10000 if bounded else None, max_crushes=None,
                  sector_order='diversified', sector_quantum=64)
    lp = dict(common, sector_method='lp', lp_strategy='envelope',
              max_pivots=10000, max_anchors=10000)
    return dict(adaptive_disc=dict(adaptive=True),
                prior_vertex_q=dict(common, sector_method='corners'), prior_vertex_lp=lp,
                tree_restricted=dict(lp, sector_method='tree', tree_model='restricted', max_tree_nodes=256),
                tree_source=dict(lp, sector_method='tree', tree_model='source', max_tree_nodes=256))


def run_query(diagram, arm, baseline, config, *, check=lambda: None):
    if arm == 'adaptive_disc':
        return fixed_source_disc_query(diagram, **config)
    producer = baseline.recognize_by_crushing if arm.startswith('prior_') else recognize_by_crushing
    return producer(diagram, check=check, **config)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', required=True)
    parser.add_argument('--pairs', type=int, default=9)
    parser.add_argument('--aa', type=int, default=3)
    parser.add_argument('--batch', type=int, default=3)
    args = parser.parse_args()
    if min(args.pairs, args.aa, args.batch) < 1:
        parser.error('pairs, aa and batch must be positive')
    baseline, configs, rng = load_baseline(), arm_configs(), Random(SEED)
    output = dict(passed=False, source_sha256=source_hashes(), baseline=baseline_pin(),
        pairs=args.pairs, aa=args.aa, batch=args.batch, seed=SEED, python=sys.version,
        platform=platform.platform(), arms=ARMS, configs=configs,
        scope='two complete positive diagram queries; native construction, shelling, search, internal replay and serialization timed; imports, diagram objects and separate independent warmup replay excluded',
        validation='every timed serialized result must match its independently verified warmup',
        records=[])
    target = Path(args.output)

    def query(diagram, arm):
        result = run_query(diagram, arm, baseline, configs[arm])
        assert result['status'] == 'UNKNOT'
        encoded = encode_result(result)
        return result, len(encoded), sha256(encoded).hexdigest()

    def sample(diagram, arm, expected):
        start = perf_counter_ns()
        for _ in range(args.batch):
            result, size, digest = query(diagram, arm)
            assert digest == expected
        return dict(ns=(perf_counter_ns()-start)/args.batch, stats=result['stats'],
                    result_bytes=size, output_sha256=digest)

    for name, diagram in [('circle', Diagram.from_pd([])),
                          ('negative_curl', Diagram.from_braid(2, [-1]))]:
        record = dict(id=name, input_pd=[list(row) for row in diagram.pd],
                      warmup_results={}, warmup_sha256={}, samples=[], aa_samples=[])
        for arm in ARMS:
            result, _, digest = query(diagram, arm)
            assert verify_result(diagram, result, arm) == 'recognition'
            record['warmup_results'][arm] = result
            record['warmup_sha256'][arm] = digest
        for _ in range(args.pairs):
            order = list(ARMS); rng.shuffle(order)
            record['samples'].append(dict(order=order, results={arm:
                sample(diagram, arm, record['warmup_sha256'][arm]) for arm in order}))
        for _ in range(args.aa):
            order = ['A', 'B']; rng.shuffle(order)
            record['aa_samples'].append(dict(order=order, results={label:
                sample(diagram, 'adaptive_disc', record['warmup_sha256']['adaptive_disc'])
                for label in order}))
        record['median_ns'] = {arm: median(s['results'][arm]['ns'] for s in record['samples'])
                               for arm in ARMS}
        record['paired_ratio'] = {f'{left}_over_{right}': median(
            s['results'][left]['ns']/s['results'][right]['ns'] for s in record['samples'])
            for left, right in [('adaptive_disc', 'tree_source'), ('prior_vertex_q', 'tree_source'),
                                ('prior_vertex_lp', 'tree_source'), ('tree_restricted', 'tree_source')]}
        record['aa_ratio'] = median(s['results']['A']['ns']/s['results']['B']['ns']
                                    for s in record['aa_samples'])
        output['records'].append(record)
        target.write_text(json.dumps(output, indent=2)+'\n')
        print(name, record['median_ns'], record['paired_ratio'], flush=True)
    assert output['source_sha256'] == source_hashes(), 'benchmarked source changed'
    output['passed'] = True
    target.write_text(json.dumps(output, indent=2)+'\n')


if __name__ == '__main__':
    main()
