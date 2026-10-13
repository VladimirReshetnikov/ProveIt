"""Replay saved candidate-policy evidence without Regina, discovery or timings.

The supplied STANDARD lists are checked ray by ray. Completeness remains the
fresh Regina enumeration's finite evidence. Retained formal ray witnesses and
complete negative trees independently establish exact h on labelled sources.
"""
import argparse
from collections import Counter
from hashlib import sha256
import json
from pathlib import Path
from random import Random
from statistics import median

from fastunknot.normal_euler_tree_verify import verify_euler_branch_tree
from fastunknot.normal_surface_geometry import _prepare
from euler_tree_research.check_evidence import positive_observation, crushing_comparison
from euler_tree_research.fixtures import supplied_cases, diagram_cases
from euler_crushing_research.benchmark import verify_result
from euler_transversal_research.check_evidence import (
    check_audit as check_supplied_geometry, check_sample)
from euler_transversal_research.common import DIAGRAM_CONFIG as LEGACY_GEOMETRY_CONFIG
from euler_transversal_research.formal import lower_bound_record
from .benchmark import expected_status
from .common import ROOT, POLICIES, STRATEGIES, SEED, configs, digest, source_hashes, lower_fixtures


def check_work(stats, policy):
    for name in ('hitting_subsets_tested','transversal_candidates','transversal_restarts',
                 'learned_conflicts','maximum_transversal_size','maximum_conflict_size',
                 'peak_cached_conflicts','conflict_cache_evictions','nodes_attempted',
                 'lp_calls','lp_pivots','anchors_tested','lp_ellipsoid_iterations',
                 'lp_feasibility_calls'):
        assert type(stats[name]) is int and stats[name] >= 0, name
    assert stats['hitting_subsets_tested'] >= stats['transversal_candidates'] >= stats['transversal_restarts']
    assert stats['learned_conflicts'] >= stats['peak_cached_conflicts']
    assert stats['learned_conflicts'] >= stats['conflict_cache_evictions']
    if policy == 'conflicts':
        assert stats['peak_cached_conflicts'] <= 256


def check_diagram(record, diagram, fixture):
    name,policy = record['id'],record['policy']
    assert record['input_pd'] == [list(row) for row in diagram.pd]
    assert record['config'] == configs()[policy]
    result = record['result']
    assert result['status'] in (expected_status(name),'INCONCLUSIVE')
    check_work(result['stats'],policy)
    assert verify_result(diagram,result,policy) == record['independent_verification']
    if result['status'] == 'INCONCLUSIVE':
        assert 'certificate' not in result and record['exact_transversal'] is None
        chain = result['partial_chain']
    else:
        assert result['certificate']['status'] == result['status']
        chain = result['certificate']['chain']
    source = chain['shelling']['triangulation']
    comparisons = record['labelled_quotient_comparisons']
    assert len(comparisons) == len(chain['steps'])
    for packet,retained in zip(chain['steps'],comparisons):
        assert retained['source'] == source and retained['source_sha256'] == digest(source)
        positive_observation(_prepare(source,lambda:None),packet['coordinates'],retained['positive_regina'])
        assert crushing_comparison(source,retained['crushing']) == packet
        source = packet['successor']
    assert source == chain['triangulation']
    if source is None:
        assert record['successor_regina'] is None and record['exact_transversal'] is None
    else:
        prepared = _prepare(source,lambda:None)
        assert record['successor_regina'] == dict(tetrahedra=len(source['tetrahedra']),
            vertices=prepared['vertices'],valid=True,orientable=True)
        if result['status'] == 'KNOTTED':
            lower = lower_bound_record(source,fixture)
            tree = result['certificate']['exhaustion']
            assert verify_euler_branch_tree(source,tree)
            resolving = sorted({node['tetrahedron'] for node in tree['nodes'] if node['kind'] == 'split'})
            assert len(resolving) == lower['lower_bound']
            exact = dict(lower,upper_bound=len(resolving),exact_h=len(resolving),
                resolving_set=resolving,negative_tree_sha256=digest(tree),
                witness_origin='retained rays freshly replayed; no fresh exhaustive root-ray enumeration')
            assert record['exact_transversal'] == exact
        else:
            assert record['exact_transversal'] is None
    return len(comparisons)


def check_audit(audit, *, require_diagrams=True):
    assert audit['policies'] == list(POLICIES) and audit['strategies'] == list(STRATEGIES)
    assert audit['diagram_configs'] == configs()
    assert set(audit['supplied_summaries']) == set(POLICIES)
    assert len(audit['supplied']) == len(list(supplied_cases())) == 88
    for record in audit['supplied']:
        assert set(record['results']) == set(POLICIES)
        for policy in POLICIES:
            assert set(record['results'][policy]) == set(STRATEGIES)
            for answer in record['results'][policy].values():
                result = answer['result']
                check_work(result['stats'],policy)
                if result['status'] == 'NO_POSITIVE_EULER':
                    chosen = result['resolving_set']
                    assert type(chosen) is list and chosen == sorted(set(chosen))
                    assert all(type(t) is int and 0 <= t < len(
                        audit['standard_vertex_oracles'][record['source_sha256']]['source']['tetrahedra'])
                        for t in chosen)
                    splits = {node['tetrahedron'] for node in result['certificate']['nodes'] if node['kind'] == 'split'}
                    assert splits <= set(chosen)
    for policy in POLICIES:
        # This view invokes the unchanged geometry checker only on supplied
        # sources, masks, exact coordinates and proofs. No diagram or policy
        # assertion is delegated: those are checked directly in this module.
        projection = dict(strategies=list(STRATEGIES), diagram_config=LEGACY_GEOMETRY_CONFIG,
            standard_vertex_oracles=audit['standard_vertex_oracles'],
            supplied=[dict(record,results=record['results'][policy]) for record in audit['supplied']],
            diagrams=[],summary=audit['supplied_summaries'][policy])
        check_supplied_geometry(projection,require_diagrams=False)
    expected = list(diagram_cases())
    expected_keys = [(name,policy) for name,_ in expected for policy in POLICIES]
    keys = [(record['id'],record['policy']) for record in audit['diagrams']]
    assert len(set(keys)) == len(keys) and set(keys) <= set(expected_keys)
    if require_diagrams:
        assert keys == expected_keys
    diagrams = dict(expected)
    fixtures = {item['id']:item for item in lower_fixtures()}
    oracles = audit['standard_vertex_oracles']
    counts = Counter(supplied_masks=len(audit['supplied']),
        supplied_queries=len(audit['supplied'])*len(POLICIES)*len(STRATEGIES),
        oracle_sources=len(oracles),original_standard_vertices=sum(len(o['vertices']) for o in oracles.values()))
    for record in audit['diagrams']:
        quotients = check_diagram(record,diagrams[record['id']],fixtures.get(record['id']))
        counts['diagram_'+record['result']['status']] += 1
        counts['diagram_labelled_quotient_equal'] += quotients
        if record['exact_transversal'] is not None:
            counts['exact_transversal_instances'] += 1
            counts['positive_root_ray_replays'] += len(record['exact_transversal']['witness_observations'])
    assert dict(counts) == audit['summary']
    return counts


def check_benchmark(benchmark, audit=None):
    assert benchmark['arms'] == list(POLICIES) and benchmark['configs'] == configs()
    assert benchmark['seed'] == SEED and benchmark['aa_arm'] == 'subsets'
    for field in ('pairs','aa','batch'):
        assert type(benchmark[field]) is int and benchmark[field] > 0
    cases = list(diagram_cases())
    assert [record['id'] for record in benchmark['records']] == [name for name,_ in cases]
    audit_results = (None if audit is None else
        {(record['id'],record['policy']):record['result'] for record in audit['diagrams']})
    rng = Random(SEED)
    table = [r'\begin{tabular}{lrrrrl}',r'\toprule',
             r'Case & Subsets (ms) & Conflicts (ms) & Subsets/conflicts & A/A & Outcomes \\',r'\midrule']
    for record,(name,diagram) in zip(benchmark['records'],cases):
        assert record['input_pd'] == [list(row) for row in diagram.pd]
        assert len(record['samples']) == benchmark['pairs']
        assert len(record['aa_samples']) == benchmark['aa']
        assert set(record['warmup_results']) == set(record['warmup_sha256']) == set(POLICIES)
        assert set(record['median_ns']) == set(POLICIES)
        for policy in POLICIES:
            result = record['warmup_results'][policy]
            assert result['status'] == expected_status(name)
            assert verify_result(diagram,result,policy) == 'recognition'
            check_work(result['stats'],policy)
            assert digest(result) == record['warmup_sha256'][policy]
            assert median(s['results'][policy]['ns'] for s in record['samples']) == record['median_ns'][policy]
            if audit_results is not None:
                assert result == audit_results[(name,policy)], 'warmup differs from separately audited query'
        for sample in record['samples']:
            order = list(POLICIES)
            rng.shuffle(order)
            assert sample['order'] == order and set(sample['results']) == set(POLICIES)
            for policy in POLICIES:
                check_sample(sample['results'][policy],record['warmup_results'][policy],
                             record['warmup_sha256'][policy],benchmark['batch'])
        ratio = median(s['results']['subsets']['ns']/s['results']['conflicts']['ns']
                       for s in record['samples'])
        assert ratio == record['paired_subsets_over_conflicts']
        for sample in record['aa_samples']:
            order = ['A','B']
            rng.shuffle(order)
            assert sample['order'] == order and set(sample['results']) == {'A','B'}
            for value in sample['results'].values():
                check_sample(value,record['warmup_results']['subsets'],record['warmup_sha256']['subsets'],benchmark['batch'])
        assert median(s['results']['A']['ns']/s['results']['B']['ns'] for s in record['aa_samples']) == record['aa_ratio']
        escaped = name.replace('_',r'\_')
        times = ' & '.join(f"{record['median_ns'][policy]/1e6:.3f}" for policy in POLICIES)
        outcomes = 'U/U' if name == 'circle' else 'K/K'
        table.append(f"{escaped} & {times} & {ratio:.3f} & {record['aa_ratio']:.3f} & {outcomes} "+r'\\')
    return '\n'.join(table+[r'\bottomrule',r'\end{tabular}'])+'\n'


def check_boundary_evidence():
    # The accompanying boundary article uses these finite counterexamples.
    # Recompute the solver-free replay and require current pins, rather than
    # publishing stale generated evidence merely because its files exist.
    from boundary_transversal_research.common import load, source_hashes as boundary_pins
    from boundary_transversal_research.replay import audit as replay_boundary
    fresh = replay_boundary()
    pins = boundary_pins()
    assert fresh['source_sha256'] == pins
    data = ROOT/'synthesis/data'
    for name in ('boundary-transversal-audit.json','boundary-transversal-replay.json'):
        assert json.loads((data/name).read_text()) == fresh, name+' is stale'
    regeneration = json.loads((data/'boundary-transversal-regeneration.json').read_text())
    assert regeneration['passed'] is True and regeneration['source_sha256'] == pins
    assert regeneration['matches_retained'] is True
    assert regeneration['records'] == load('provenance/layer-refuter.json')['records']
    return dict(source_count=len(pins), endpoint_rays=sum(len(r['witnesses'])
        for r in fresh['endpoints']), layers=sum(len(r['steps']) for r in fresh['layered']))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--audit',type=Path,default=ROOT/'synthesis/data/conflict-candidate-audit.json')
    parser.add_argument('--benchmark',type=Path)
    parser.add_argument('--supplied-only',action='store_true')
    parser.add_argument('--publication',action='store_true')
    args = parser.parse_args()
    pins = source_hashes()
    audit = json.loads(args.audit.read_text())
    assert audit['passed'] is True and audit['source_sha256'] == pins, 'audit source pins stale'
    counts = check_audit(audit,require_diagrams=not args.supplied_only)
    benchmark = None
    if args.benchmark is not None:
        benchmark = json.loads(args.benchmark.read_text())
        assert benchmark['passed'] is True and benchmark['source_sha256'] == pins, 'benchmark source pins stale'
        table = check_benchmark(benchmark,audit)
        (ROOT/'synthesis/data/conflict-candidate-table.tex').write_text(table)
    assert source_hashes() == pins, 'replayed sources changed'
    if args.publication:
        assert not args.supplied_only and benchmark is not None
        assert (benchmark['pairs'],benchmark['aa'],benchmark['batch']) == (5,1,1)
        data = ROOT/'synthesis/data'
        files = {ROOT/name for name in pins}
        boundary = check_boundary_evidence()
        for pattern in ('conflict-candidate-*','conflict-candidates-*','boundary-transversal-*'):
            files.update(data.glob(pattern))
        for pattern in ('test*crushing*.py','test*euler*.py','test*sector*.py',
                        'test*positive_ray*.py','test_normal_vertex_reduction.py',
                        'test*source_kernel*.py','test*polynomial*lp*.py'):
            files.update((ROOT/'fast/tests').glob(pattern))
        required = {ROOT/'fast/README.md',ROOT/'synthesis/README.md',
                    ROOT/'fast/tests/test_conflict_candidates.py'}
        required.update(ROOT/'synthesis'/name for name in (
            'conflict_candidates.tex','boundary_transversal.tex','euler_transversal.tex',
            'marked_cut_handlebodies.tex','report.pdf'))
        assert all(path.is_file() for path in required)
        files.update(required)
        target = data/'conflict-candidate-publication.json'
        target.write_text(json.dumps(dict(passed=True,counts=dict(counts),
            boundary_replay=boundary,
            finite_complete_branching=True,finite_exact_transversal_numbers=True,
            general_quasipolynomial=False,source_sha256={str(path.relative_to(ROOT)):
                sha256(path.read_bytes()).hexdigest() for path in sorted(files)
                if path.is_file() and path != target}),indent=2)+'\n')
    print('PASS',dict(counts),'saved proofs, finite h, oracle comparisons and source pins checked')


if __name__ == '__main__':
    main()
