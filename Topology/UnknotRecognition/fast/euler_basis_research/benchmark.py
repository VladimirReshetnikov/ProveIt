"""Paired complete recognition with exact row reduction and replay caching ablations."""
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
from unittest.mock import patch

from fastunknot.diagram import Diagram
from fastunknot import exact_lp, normal_euler_tree, normal_euler_tree_verify
from fastunknot import normal_crushing_search as driver
from euler_crushing_research.benchmark import encode_result, verify_result
from .replay_benchmark import ROOT, source_hashes

BASELINE_COMMIT = '1c1665d2ca69fac24d3a1b2707917b3c209706e1'
BASELINE_FILES = [
    dict(path='Topology/UnknotRecognition/fast/fastunknot/exact_lp.py',
         sha256='c1e2f3bcb807a3902db0cb2c5df5385a6df7fc67a399dbe9fa3dc251302279a8'),
    dict(path='Topology/UnknotRecognition/fast/fastunknot/normal_euler_tree_verify.py',
         sha256='dcfc8e80c8444ceb13159e5a2848dcd4a0ad1a45e0ef1f3fba8db7144c0d2e70')]
ARMS = ('prior', 'row_basis', 'replay_cache', 'combined')
SEED = 2026101206
CONFIG = dict(sector_method='tree', tree_model='source', reduce_vertices=True,
              max_tree_nodes=256, max_pivots=10000, max_anchors=10000)


def baseline_pin():
    return dict(commit=BASELINE_COMMIT, files=BASELINE_FILES,
                scope='historical exact LP and tree verifier modules; shared driver and dependencies use current pinned files')


def load_baseline():
    modules = []
    for record in BASELINE_FILES:
        raw = subprocess.run(['git', 'show', f"{BASELINE_COMMIT}:{record['path']}"],
                             cwd=ROOT, check=True, capture_output=True).stdout
        assert sha256(raw).hexdigest() == record['sha256']
        module = ModuleType('fastunknot._basis_prior_'+Path(record['path']).stem)
        module.__package__ = 'fastunknot'
        module.__file__ = f"git:{BASELINE_COMMIT}:{record['path']}"
        exec(compile(raw, module.__file__, 'exec'), module.__dict__)
        modules.append(module)
    return modules


def run_query(diagram, arm, baseline):
    old_lp, old_verifier = baseline
    solver = (exact_lp.solve_nonnegative_kernel if arm in ('row_basis', 'combined')
              else old_lp.solve_nonnegative_kernel)
    verifier = (normal_euler_tree_verify.verify_euler_branch_tree if arm in ('replay_cache', 'combined')
                else old_verifier.verify_euler_branch_tree)
    with patch.object(normal_euler_tree, 'solve_nonnegative_kernel', solver):
        with patch.object(driver, 'verify_euler_branch_tree', verifier):
            return driver.recognize_by_crushing(diagram, **CONFIG)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', required=True)
    parser.add_argument('--pairs', type=int, default=5)
    parser.add_argument('--aa', type=int, default=1)
    parser.add_argument('--batch', type=int, default=1)
    args = parser.parse_args()
    if min(args.pairs, args.aa, args.batch) < 1:
        parser.error('pairs, aa and batch must be positive')
    baseline, rng = load_baseline(), Random(SEED)
    output = dict(passed=False, source_sha256=source_hashes(), baseline=baseline_pin(),
        pairs=args.pairs, aa=args.aa, batch=args.batch, seed=SEED, python=sys.version,
        platform=platform.platform(), arms=ARMS, config=CONFIG,
        scope='complete circle and trefoil recognition; construction, shelling, preprocessing, discovery, internal replay, patch setup and serialization timed; imports, diagram objects and independent warmup replay excluded',
        records=[])
    target = Path(args.output)

    def query(diagram, arm):
        result = run_query(diagram, arm, baseline)
        assert result['status'] in ('UNKNOT', 'KNOTTED')
        encoded = encode_result(result)
        return result, len(encoded), sha256(encoded).hexdigest()

    def sample(diagram, arm, expected):
        start = perf_counter_ns()
        for _ in range(args.batch):
            result, size, digest = query(diagram, arm)
            assert digest == expected
        return dict(ns=(perf_counter_ns()-start)/args.batch, stats=result['stats'],
                    result_bytes=size, output_sha256=digest)

    for name, diagram, status in [('circle', Diagram.from_pd([]), 'UNKNOT'),
                                  ('trefoil', Diagram.from_braid(2, [1, 1, 1]), 'KNOTTED')]:
        record = dict(id=name, input_pd=[list(row) for row in diagram.pd],
                      warmup_results={}, warmup_sha256={}, samples=[], aa_samples=[])
        for arm in ARMS:
            result, _, digest = query(diagram, arm)
            assert result['status'] == status
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
                sample(diagram, 'prior', record['warmup_sha256']['prior']) for label in order}))
        record['median_ns'] = {arm: median(s['results'][arm]['ns'] for s in record['samples'])
                               for arm in ARMS}
        record['paired_ratio'] = {f'{left}_over_combined': median(
            s['results'][left]['ns']/s['results']['combined']['ns'] for s in record['samples'])
            for left in ARMS[:-1]}
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
