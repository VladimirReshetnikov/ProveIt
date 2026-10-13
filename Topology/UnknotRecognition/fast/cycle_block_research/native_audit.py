"""Authenticated native matrices; partial plans are not geometric successors."""
from collections import Counter
import hashlib
import importlib.util
import json
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[2]
sys.path[:0] = [str(ROOT/'fast'), str(ROOT/'reports/110'), str(ROOT/'reports/116')]
from cycleblocks.transport import deferred_forest
from cycleblocks.core import optimize_counts as delivered_optimize
from fastunknot.cycle_block_cancellation import optimize_counts, verify_plan
from fastunknot.normal_parallelity import normal_cut_parallelity
from fastunknot.normal_parallelity_verify import verify_normal_cut_parallelity
from fastunknot.core_three_handle_reduction import reduce_core_three_handles
from fastunknot.core_three_handle_reduction_verify import replay_core_three_handles

spec = importlib.util.spec_from_file_location('ordered_adapter', ROOT/'reports/110/integration/occurrence_adapter.py')
ordered = importlib.util.module_from_spec(spec)
spec.loader.exec_module(ordered)


def cases():
    answer = [c for name in ('corpus.json', 'three_handle_corpus.json')
              for c in json.loads((ROOT/'fast/marked_parallelity_research'/name).read_text())['cases']]
    added = json.loads((ROOT/'fast/signed_annulus_research/corpus.json').read_text())
    return answer + added['cases'] + added['refusals']


def main():
    out = Path(sys.argv[1])
    report = dict(passed=False, scope=__doc__, records=[], source_sha256={
        str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest()
        for folder in ('fast/fastunknot', 'reports/110/pivotwidth', 'reports/116/cycleblocks')
        for p in sorted((ROOT/folder).glob('*.py'))})
    for case in cases():
        p = normal_cut_parallelity(case['triangulation'], case['coordinates'], record_certificate=True)
        assert p['status'] == 'COMPLETE'
        assert verify_normal_cut_parallelity(case['triangulation'], case['coordinates'], p['certificate'])
        g, reduction = reduce_core_three_handles(p['geometry'], strategy='max_weight')
        assert replay_core_three_handles(p['geometry'], reduction) == g
        counts = {h['id']:dict(Counter(x['handle'] for x in h['cycle'] if x['dimension']==1)) for h in g['core']['handles2']}
        result = optimize_counts(counts)
        assert result['status'] == 'OPTIMAL_MATRIX_PLAN', (case['id'], result)
        assert verify_plan(counts, result)
        old = ordered.propose_occurrence_reduction(counts)
        assert old['status'] == 'REDUCTION_PLAN', (case['id'],old)
        assert old['deferred_weight'] == result['deferred_weight']
        delivered = delivered_optimize(counts)
        if delivered['status'] == 'OPTIMAL_MATRIX_PLAN':
            assert delivered['deferred_weight'] == result['deferred_weight']
        forest = deferred_forest(len(g['core']['handles0']), {h['id']:h['ends'] for h in g['core']['handles1']}, counts, result)
        report['records'].append(dict(id=case['id'], counts=counts, plan=result, forest=forest,
            ordered=old, delivered=delivered, source_authenticated=True, geometric_partial_cancellation=False))
        print(len(report['records']),case['id'],'deferred',result['deferred_weight'],
              'block rank',result['stats']['max_block_rank'],flush=True)
        out.write_text(json.dumps(report,indent=2)+'\n')
    report['passed'] = True
    out.write_text(json.dumps(report,indent=2)+'\n')


if __name__ == '__main__': main()
