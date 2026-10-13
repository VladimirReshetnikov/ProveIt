"""Paired complete matrix queries; excludes native geometry construction.

Each query includes input normalization, discovery, feasible-plan replay and
JSON serialization. Neither replay certifies an arbitrary producer's optimum.
"""
import gc
import hashlib
import json
from pathlib import Path
import random
import statistics
import sys
import time
from native_audit import ROOT, ordered
from cycleblocks import core as baseline
from fastunknot import cycle_block_cancellation as maintained


def query(mode, counts):
    if mode == 'ordered':
        result = ordered.propose_occurrence_reduction(counts, state_limit=None)
        assert result['status'] == 'REDUCTION_PLAN'
    else:
        module = baseline if mode == 'delivered' else maintained
        result = module.optimize_counts(counts, limits=module.Limits(max_work=2_000_000, max_block_rank=None,
            max_paths=256 if mode == 'delivered' else None))
        assert result['status'] in ('OPTIMAL_MATRIX_PLAN','RESOURCE_LIMIT')
        if result['status'] == 'OPTIMAL_MATRIX_PLAN': assert module.verify_plan(counts, result)
    json.dumps(result, sort_keys=True, separators=(',', ':'))
    return result


def main():
    rng = random.Random(11620261013)
    native = json.loads((ROOT/'synthesis/data/cycle-block-native-audit.json').read_text())
    inputs = [(r['id'], {int(k):{int(c):a for c,a in row.items()} for k,row in r['counts'].items()})
              for r in native['records'] if r['id'] in ('nested_1_4_6/interior_links', 'interior_loop/interior_links', 'pachner23_5_8_3/mixed')]
    inputs += [('cactus/128', {r:{0:1,r//2+1:1} for r in range(256)}),
               ('K2,48', {r:dict.fromkeys(range(48),1) for r in range(2)})]
    report = dict(scope=__doc__, seed=11620261013, rounds=9, aa_rounds=3, cases=[],
        source_sha256={str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest()
          for p in [Path(__file__), ROOT/'fast/fastunknot/cycle_block_cancellation.py',
                    ROOT/'reports/116/cycleblocks/core.py',ROOT/'reports/110/pivotwidth/core.py',
                    ROOT/'reports/110/pivotwidth/preprocess.py', ROOT/'reports/110/pivotwidth/verify.py',
                    ROOT/'reports/110/integration/occurrence_adapter.py']})
    for name, counts in inputs:
        answers = {mode:query(mode,counts) for mode in ('delivered','maintained','ordered')}
        assert len({a['deferred_weight'] for a in answers.values() if 'deferred_weight' in a}) == 1
        pilot = []
        for mode in answers:
            start=time.perf_counter_ns(); query(mode,counts); pilot.append(time.perf_counter_ns()-start)
        batch=max(1,min(64,int(5_000_000/max(pilot))))
        def measure(mode):
            gc.collect()
            start=time.perf_counter_ns()
            for _ in range(batch): query(mode,counts)
            return (time.perf_counter_ns()-start)/batch
        pairs=[]
        for _ in range(9):
            order=list(answers); rng.shuffle(order)
            pairs.append(dict(order=order, samples_ns={mode:measure(mode) for mode in order}))
        aa=[[measure('maintained'),measure('maintained')] for _ in range(3)]
        row=dict(id=name,batch=batch, rows=len(counts), nonzeros=sum(map(len,counts.values())),
            input_sha256=hashlib.sha256(json.dumps(counts,sort_keys=True).encode()).hexdigest(),
            answers=answers, pairs=pairs, aa_samples_ns=aa,
            median_ms={mode:statistics.median(x['samples_ns'][mode] for x in pairs)/1e6 for mode in answers},
            paired_delivered_over_maintained=(statistics.median(x['samples_ns']['delivered']/x['samples_ns']['maintained'] for x in pairs)
                if answers['delivered']['status']=='OPTIMAL_MATRIX_PLAN' else None),
            paired_ordered_over_maintained=statistics.median(x['samples_ns']['ordered']/x['samples_ns']['maintained'] for x in pairs),
            aa_ratio=statistics.median(a/b for a,b in aa))
        report['cases'].append(row)
        print(name,row['median_ms'], 'D/M',row['paired_delivered_over_maintained'], 'O/M',row['paired_ordered_over_maintained'],flush=True)
    (ROOT/'synthesis/data/cycle-block-benchmark.json').write_text(json.dumps(report,indent=2)+'\n')


if __name__ == '__main__': main()
