"""Replay saved row-basis/replay-cache evidence and prepare publication tables.

No surface discovery, LP solve, Regina import or new timing is performed.
Saved finite oracle comparisons use the independent Euler-tree audit checker.
Historical verifier code is loaded only to replay the same retained proof.
"""
import argparse
from hashlib import sha256
import json
from math import isfinite
from random import Random
from statistics import median
import subprocess
from unittest.mock import patch

from fastunknot.diagram import Diagram
from fastunknot import normal_crushing_search as driver
from fastunknot.normal_euler_tree_verify import verify_euler_branch_tree
from euler_crushing_research.benchmark import verify_result
from euler_tree_research.check_evidence import check_audit
from . import replay_benchmark as replay


ROOT = replay.ROOT
ARMS = ('prior', 'row_basis', 'replay_cache', 'combined')


def digest(path):
    return sha256(path.read_bytes()).hexdigest()


def object_digest(value):
    return sha256(replay.encode(value)).hexdigest()


def positive_number(value):
    assert type(value) in (int, float) and isfinite(value) and value > 0


def repetitions(record):
    for field in ('pairs', 'aa', 'batch'):
        assert type(record[field]) is int and record[field] > 0


def check_baseline(baseline):
    assert baseline['commit'] == replay.BASELINE_COMMIT
    expected_paths = {
        'Topology/UnknotRecognition/fast/fastunknot/exact_lp.py', replay.BASELINE_PATH}
    assert type(baseline['files']) is list and len(baseline['files']) == 2
    assert {item['path'] for item in baseline['files']} == expected_paths
    for item in baseline['files']:
        assert set(item) == {'path', 'sha256'}
        raw = subprocess.run(['git', 'show', f"{replay.BASELINE_COMMIT}:{item['path']}"],
                             cwd=ROOT, check=True, capture_output=True).stdout
        assert sha256(raw).hexdigest() == item['sha256']


def check_query_sample(sample, result, expected_hash):
    positive_number(sample['ns'])
    assert sample['stats'] == result['stats']
    assert type(sample['result_bytes']) is int and sample['result_bytes'] == len(replay.encode(result))
    assert sample['output_sha256'] == expected_hash


def check_benchmark(benchmark):
    from .benchmark import SEED, CONFIG, baseline_pin
    assert benchmark['baseline'] == baseline_pin()
    check_baseline(benchmark['baseline'])
    repetitions(benchmark)
    assert benchmark['arms'] == list(ARMS) and benchmark['seed'] == SEED
    assert benchmark['config'] == CONFIG
    assert [record['id'] for record in benchmark['records']] == ['circle', 'trefoil']
    diagrams = {'circle': Diagram.from_pd([]), 'trefoil': Diagram.from_braid(2, [1, 1, 1])}
    rng = Random(SEED)
    ratios = [(arm, 'combined') for arm in ARMS[:-1]]
    table = [r'\begin{tabular}{lrrrrrr}', r'\toprule',
        r'Case & Prior & Row basis & Replay cache & Combined & Prior/combined & A/A \\', r'\midrule']
    for record in benchmark['records']:
        diagram = diagrams[record['id']]
        expected_status = 'UNKNOT' if record['id'] == 'circle' else 'KNOTTED'
        assert record['input_pd'] == [list(row) for row in diagram.pd]
        assert set(record['warmup_results']) == set(record['warmup_sha256']) == set(ARMS)
        assert set(record['median_ns']) == set(ARMS)
        assert len(record['samples']) == benchmark['pairs']
        assert len(record['aa_samples']) == benchmark['aa']
        for arm in ARMS:
            result = record['warmup_results'][arm]
            assert result['status'] == result['certificate']['status'] == expected_status
            assert verify_result(diagram, result, arm) == 'recognition'
            assert object_digest(result) == record['warmup_sha256'][arm]
        assert record['warmup_sha256']['prior'] == record['warmup_sha256']['replay_cache']
        assert record['warmup_sha256']['row_basis'] == record['warmup_sha256']['combined']
        if record['id'] == 'circle':
            assert len(set(record['warmup_sha256'].values())) == 1
        for sample in record['samples']:
            order = list(ARMS); rng.shuffle(order)
            assert sample['order'] == order and set(sample['results']) == set(ARMS)
            for arm in ARMS:
                check_query_sample(sample['results'][arm], record['warmup_results'][arm], record['warmup_sha256'][arm])
        for arm in ARMS:
            assert median(sample['results'][arm]['ns'] for sample in record['samples']) == record['median_ns'][arm]
        assert set(record['paired_ratio']) == {f'{left}_over_{right}' for left, right in ratios}
        for left, right in ratios:
            assert median(sample['results'][left]['ns']/sample['results'][right]['ns']
                          for sample in record['samples']) == record['paired_ratio'][f'{left}_over_{right}']
        for sample in record['aa_samples']:
            order = ['A', 'B']; rng.shuffle(order)
            assert sample['order'] == order and set(sample['results']) == {'A', 'B'}
            for value in sample['results'].values():
                check_query_sample(value, record['warmup_results']['prior'], record['warmup_sha256']['prior'])
        assert median(sample['results']['A']['ns']/sample['results']['B']['ns']
                      for sample in record['aa_samples']) == record['aa_ratio']
        values = ' & '.join(f"{record['median_ns'][arm]/1e6:.3f}" for arm in ARMS)
        table.append(f"{record['id']} & {values} & {record['paired_ratio']['prior_over_combined']:.3f} & {record['aa_ratio']:.3f} "+r'\\')
    return '\n'.join(table+[r'\bottomrule', r'\end{tabular}'])+'\n'


def check_replay_sample(sample, batch):
    positive_number(sample['ns'])
    assert type(sample['elapsed_ns']) is int and sample['elapsed_ns'] > 0
    assert sample['ns'] == sample['elapsed_ns']/batch
    assert type(sample['results']) is list and len(sample['results']) == batch
    assert all(value is True for value in sample['results'])
    assert sample['output_sha256'] == object_digest(sample['results'])


def check_replay(record):
    assert record['baseline'] == replay.baseline_pin()
    assert record['benchmark_sha256'] == digest(ROOT/'fast/euler_basis_research/replay_benchmark.py')
    assert record['source_certificate'] == dict(path=replay.EVIDENCE_PATH,
        sha256=replay.EVIDENCE_SHA256, case_id='trefoil')
    repetitions(record)
    assert record['arms'] == list(replay.ARMS) and record['metrics'] == list(replay.METRICS)
    assert record['seed'] == replay.SEED
    input_pd, certificate = replay.load_input()
    source, tree = certificate['chain']['triangulation'], certificate['exhaustion']
    diagram = Diagram.from_pd(input_pd)
    assert record['input_pd'] == input_pd
    assert record['certificate_sha256'] == object_digest(certificate)
    assert record['tree_sha256'] == object_digest(tree)
    assert record['final_source_sha256'] == object_digest(source)
    assert record['certificate_bytes'] == len(replay.encode(certificate))
    assert record['tree_bytes'] == len(replay.encode(tree))
    assert record['source_tetrahedra'] == len(source['tetrahedra'])
    assert record['tree_nodes'] == len(tree['nodes'])
    assert record['negative_leaves'] == sum(node['kind'] == 'negative' for node in tree['nodes'])
    assert record['anchor_records'] == sum(len(node['certificate'].get('duals', []))
                                          for node in tree['nodes'] if node['kind'] == 'negative')
    prior = replay.load_baseline()
    for verifier in (prior.verify_euler_branch_tree, verify_euler_branch_tree):
        assert verifier(source, tree)
        with patch.object(driver, 'verify_euler_branch_tree', verifier):
            assert driver.verify_crushing_recognition(diagram, certificate)
    assert record['untimed_replay_profile'] == replay.profile_replay(source, tree)
    assert [row['metric'] for row in record['records']] == list(replay.METRICS)
    rng = Random(replay.SEED)
    table = [r'\begin{tabular}{lrrrr}', r'\toprule',
             r'Replay & Prior & Cached & Prior/cached & A/A \\', r'\midrule']
    for row in record['records']:
        assert set(row['warmups']) == set(replay.ARMS) and all(value is True for value in row['warmups'].values())
        assert set(row['median_ns']) == set(replay.ARMS)
        assert len(row['samples']) == record['pairs'] and len(row['aa_samples']) == record['aa']
        for sample in row['samples']:
            order = list(replay.ARMS); rng.shuffle(order)
            assert sample['order'] == order and set(sample['results']) == set(replay.ARMS)
            for value in sample['results'].values():
                check_replay_sample(value, record['batch'])
        for arm in replay.ARMS:
            assert median(sample['results'][arm]['ns'] for sample in row['samples']) == row['median_ns'][arm]
        assert median(sample['results']['prior']['ns']/sample['results']['cached']['ns']
                      for sample in row['samples']) == row['paired_prior_over_cached']
        for sample in row['aa_samples']:
            order = ['A', 'B']; rng.shuffle(order)
            assert sample['order'] == order and set(sample['results']) == {'A', 'B'}
            for value in sample['results'].values():
                check_replay_sample(value, record['batch'])
        assert median(sample['results']['A']['ns']/sample['results']['B']['ns']
                      for sample in row['aa_samples']) == row['aa_ratio']
        label = 'Tree' if row['metric'] == 'tree' else 'Full recognition'
        table.append(f"{label} & {row['median_ns']['prior']/1e6:.3f} & {row['median_ns']['cached']/1e6:.3f} & {row['paired_prior_over_cached']:.3f} & {row['aa_ratio']:.3f} "+r'\\')
    return '\n'.join(table+[r'\bottomrule', r'\end{tabular}'])+'\n'


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--publication', action='store_true')
    args = parser.parse_args()
    data = ROOT/'synthesis/data'
    audit, benchmark, replay_record = [json.loads((data/f'euler-basis-{name}.json').read_text())
                                      for name in ('audit', 'benchmark', 'replay')]
    pins = replay.source_hashes()
    for record in (audit, benchmark, replay_record):
        assert record['passed'] is True
        assert record['source_sha256'] == pins, 'source pins are missing, extra or stale'
        for name, expected in record['source_sha256'].items():
            assert digest(ROOT/name) == expected, name
    counts = check_audit(audit)
    query_table = check_benchmark(benchmark)
    replay_table = check_replay(replay_record)
    assert replay.source_hashes() == pins, 'checked source changed during replay'
    (data/'euler-basis-table.tex').write_text(query_table)
    (data/'euler-basis-replay-table.tex').write_text(replay_table)
    if args.publication:
        assert (benchmark['pairs'], benchmark['aa'], benchmark['batch']) == (5, 1, 1)
        assert (replay_record['pairs'], replay_record['aa'], replay_record['batch']) == (9, 3, 3)
        files = {ROOT/name for name in pins}
        files.update(data.glob('euler-basis-*'))
        for pattern in ('test*crushing*.py', 'test*euler*.py', 'test*lp*.py', 'test*sector*.py',
                        'test*positive_ray*.py', 'test_normal_vertex_reduction.py', 'test*source_kernel*.py'):
            files.update((ROOT/'fast/tests').glob(pattern))
        required = {ROOT/'fast/README.md', ROOT/replay.EVIDENCE_PATH}
        required.update(ROOT/'synthesis'/name for name in
                        ('euler_rank_replay.tex', 'marked_cut_handlebodies.tex', 'report.pdf'))
        assert all(path.is_file() for path in required)
        files.update(required)
        target = data/'euler-basis-publication.json'
        target.write_text(json.dumps(dict(passed=True, counts=dict(counts),
            exact_independent_row_basis=True, bounded_source_replay_cache=True,
            general_quasipolynomial=False, source_sha256={str(path.relative_to(ROOT)): digest(path)
            for path in sorted(files) if path.is_file() and path != target}), indent=2)+'\n')
    print('PASS', dict(counts), 'saved proofs, paired timings, replay counts and source pins checked')


if __name__ == '__main__':
    main()
