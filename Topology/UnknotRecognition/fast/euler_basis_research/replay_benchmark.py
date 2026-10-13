"""Paired replay of a fixed trefoil proof before and after bounded replay caches.

Run from fast/: python -B -m euler_basis_research.replay_benchmark --output PATH
This performs no discovery. Every timed call reconstructs its source model and
starts fresh replay caches. The exact old certificate, not a newly generated
proof, is shared by both verifier arms and retained by a pinned evidence file.
"""
import argparse
from collections import Counter
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
from fastunknot import normal_crushing_search as driver
from fastunknot import normal_euler_tree_verify as current
from euler_tree_research.benchmark import source_hashes as tree_source_hashes


ROOT = Path(__file__).resolve().parents[2]
BASELINE_COMMIT = '1c1665d2ca69fac24d3a1b2707917b3c209706e1'
BASELINE_PATH = 'Topology/UnknotRecognition/fast/fastunknot/normal_euler_tree_verify.py'
BASELINE_SHA256 = 'dcfc8e80c8444ceb13159e5a2848dcd4a0ad1a45e0ef1f3fba8db7144c0d2e70'
EVIDENCE_PATH = 'synthesis/data/euler-tree-audit.json'
EVIDENCE_SHA256 = '16cf75021d738b9102c8635a3e69f8da9cdf433d12e94154f4a8a388848ab306'
SEED = 2026101205
ARMS = ('prior', 'cached')
METRICS = ('tree', 'recognition')


def encode(value):
    return json.dumps(value, sort_keys=True, separators=(',', ':')).encode()


def digest(value):
    return sha256(value).hexdigest()


def baseline_pin():
    return dict(commit=BASELINE_COMMIT, path=BASELINE_PATH, sha256=BASELINE_SHA256,
                scope='historical Euler-tree verifier only; all shared replay dependencies use pinned current sources')


def source_hashes():
    result = tree_source_hashes()
    for path in sorted(Path(__file__).parent.iterdir()):
        if path.suffix in ('.py', '.md'):
            result[str(path.relative_to(ROOT))] = digest(path.read_bytes())
    return dict(sorted(result.items()))


def load_baseline():
    raw = subprocess.run(['git', 'show', f'{BASELINE_COMMIT}:{BASELINE_PATH}'],
                         cwd=ROOT, check=True, capture_output=True).stdout
    assert digest(raw) == BASELINE_SHA256
    prior = ModuleType('fastunknot._pinned_euler_tree_verify')
    prior.__package__ = 'fastunknot'
    prior.__file__ = f'git:{BASELINE_COMMIT}:{BASELINE_PATH}'
    exec(compile(raw, prior.__file__, 'exec'), prior.__dict__)
    return prior


def load_input():
    raw = (ROOT/EVIDENCE_PATH).read_bytes()
    assert digest(raw) == EVIDENCE_SHA256, 'saved baseline certificate evidence changed'
    audit = json.loads(raw)
    assert audit['passed'] is True
    case = next(record for record in audit['diagrams'] if record['id'] == 'trefoil')
    certificate = case['result']['certificate']
    assert case['result']['status'] == certificate['status'] == 'KNOTTED'
    return case['input_pd'], certificate


def profile_replay(source, tree):
    """Count actual arithmetic reuse after timing, without cache instrumentation inside samples."""
    counts = Counter()
    original_cached, original_model = current._cached, current._reference_model

    def cached(cache, key, build, check):
        # This fixed source has nonempty Fraction dual tuples. Anchor tuple
        # entries are literal integers; None denotes its envelope objective.
        kind = 'objective' if key is None or all(type(x) is int for x in key) else 'dual_product'
        counts[kind+'_lookups'] += 1
        counts[kind+'_hits'] += key in cache
        value = original_cached(cache, key, build, check)
        counts[kind+'_maximum_retained'] = max(counts[kind+'_maximum_retained'], len(cache))
        return value

    def model(*args, **kwargs):
        value = original_model(*args, **kwargs)
        counts['full_source_model_builds'] += 1
        counts['cycle_rows'] = len(value[0])
        counts['full_columns'] = len(value[1])
        return value

    with patch.object(current, '_cached', side_effect=cached):
        with patch.object(current, '_reference_model', side_effect=model):
            with patch.object(current, '_dual', wraps=current._dual) as parsed:
                assert current.verify_euler_branch_tree(source, tree)
                counts['parsed_dual_payloads'] = parsed.call_count
    for kind in ('objective', 'dual_product'):
        counts[kind+'_builds'] = counts[kind+'_lookups']-counts[kind+'_hits']
        assert counts[kind+'_maximum_retained'] <= 256
    return dict(counts)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', required=True)
    parser.add_argument('--pairs', type=int, default=9)
    parser.add_argument('--aa', type=int, default=3)
    parser.add_argument('--batch', type=int, default=3)
    args = parser.parse_args()
    if min(args.pairs, args.aa, args.batch) < 1:
        parser.error('pairs, aa and batch must be positive')
    prior = load_baseline()
    input_pd, certificate = load_input()
    source, tree = certificate['chain']['triangulation'], certificate['exhaustion']
    diagram = Diagram.from_pd(input_pd)
    original_hash = digest(encode(certificate))
    arms = dict(prior=prior.verify_euler_branch_tree, cached=current.verify_euler_branch_tree)
    pins = source_hashes()
    output = dict(passed=False, baseline=baseline_pin(), source_sha256=pins,
        benchmark_sha256=digest(Path(__file__).read_bytes()),
        source_certificate=dict(path=EVIDENCE_PATH, sha256=EVIDENCE_SHA256, case_id='trefoil'),
        certificate_sha256=original_hash, tree_sha256=digest(encode(tree)),
        final_source_sha256=digest(encode(source)), source_tetrahedra=len(source['tetrahedra']),
        tree_nodes=len(tree['nodes']), negative_leaves=sum(n['kind']=='negative' for n in tree['nodes']),
        anchor_records=sum(len(n['certificate'].get('duals', []))
                           for n in tree['nodes'] if n['kind']=='negative'),
        input_pd=input_pd, certificate_bytes=len(encode(certificate)), tree_bytes=len(encode(tree)),
        pairs=args.pairs, batch=args.batch, aa=args.aa, seed=SEED, arms=ARMS, metrics=METRICS,
        python=sys.version, platform=platform.platform(),
        scope='same saved trefoil negative certificate; independent replay only, no construction or search; all source preparation inside replay; loading/imports/patch setup excluded; fresh source-local cache per replay',
        records=[])
    target, rng = Path(args.output), Random(SEED)

    def save():
        target.write_text(json.dumps(output, indent=2)+'\n')

    def operation(metric, arm):
        return ((lambda: arms[arm](source, tree)) if metric == 'tree'
                else (lambda: driver.verify_crushing_recognition(diagram, certificate)))

    def sample(metric, arm):
        with patch.object(driver, 'verify_euler_branch_tree', arms[arm]):
            action = operation(metric, arm)
            started = perf_counter_ns()
            results = [action() for _ in range(args.batch)]
            elapsed = perf_counter_ns()-started
        assert all(value is True for value in results)
        assert digest(encode(certificate)) == original_hash
        return dict(ns=elapsed/args.batch, elapsed_ns=elapsed, results=results,
                    output_sha256=digest(encode(results)))

    save()
    for metric in METRICS:
        for arm in ARMS:
            with patch.object(driver, 'verify_euler_branch_tree', arms[arm]):
                assert operation(metric, arm)() is True
        record = dict(metric=metric, warmups={arm:True for arm in ARMS}, samples=[], aa_samples=[])
        for _ in range(args.pairs):
            order = list(ARMS); rng.shuffle(order)
            record['samples'].append(dict(order=order, results={arm:sample(metric, arm) for arm in order}))
        for _ in range(args.aa):
            order = ['A', 'B']; rng.shuffle(order)
            record['aa_samples'].append(dict(order=order, results={label:sample(metric, 'prior') for label in order}))
        record['median_ns'] = {arm:median(s['results'][arm]['ns'] for s in record['samples']) for arm in ARMS}
        record['paired_prior_over_cached'] = median(s['results']['prior']['ns']/s['results']['cached']['ns']
                                                     for s in record['samples'])
        record['aa_ratio'] = median(s['results']['A']['ns']/s['results']['B']['ns'] for s in record['aa_samples'])
        output['records'].append(record)
        save()
        print(metric, record['median_ns'], record['paired_prior_over_cached'], record['aa_ratio'], flush=True)
    output['untimed_replay_profile'] = profile_replay(source, tree)
    assert pins == source_hashes(), 'replayed source changed during measurement'
    assert digest(encode(certificate)) == original_hash
    assert digest((ROOT/EVIDENCE_PATH).read_bytes()) == EVIDENCE_SHA256
    output['passed'] = True
    save()


if __name__ == '__main__':
    main()
