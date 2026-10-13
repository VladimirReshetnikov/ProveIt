"""Complete matrix queries isolating cycle-prefix pruning; no deferral prepass."""
import gc
import hashlib
import json
from pathlib import Path
import random
import statistics
import time
from benchmark import ROOT, baseline, maintained


def main():
    rng=random.Random(11620261014)
    report=dict(scope=__doc__, seed=11620261014, rounds=7, cases=[],
        source_sha256={str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest()
                      for p in [Path(__file__),ROOT/'fast/fastunknot/cycle_block_cancellation.py',ROOT/'reports/116/cycleblocks/core.py']})
    for size in (16,48,96):
        counts={r:dict.fromkeys(range(size),1) for r in range(2)}
        def query(mode):
            module=baseline if mode=='delivered' else maintained
            extra={} if mode=='delivered' else dict(single_deferral=False)
            p=module.optimize_counts(counts,limits=module.Limits(max_work=None,max_block_rank=None,max_paths=256),**extra)
            assert p['status']=='OPTIMAL_MATRIX_PLAN' and p['matched_weight']==1
            assert module.verify_plan(counts,p)
            json.dumps(p,sort_keys=True,separators=(',',':'))
            return p
        answers={mode:query(mode) for mode in ('delivered','maintained')}
        def measure(mode):
            gc.collect();start=time.perf_counter_ns();query(mode)
            return time.perf_counter_ns()-start
        pairs=[]
        for _ in range(7):
            order=['delivered','maintained'];rng.shuffle(order)
            pairs.append(dict(order=order,samples_ns={mode:measure(mode) for mode in order}))
        aa=[[measure('maintained'),measure('maintained')] for _ in range(3)]
        row=dict(columns=size,answers=answers,pairs=pairs,aa_samples_ns=aa,
            median_ms={mode:statistics.median(x['samples_ns'][mode] for x in pairs)/1e6 for mode in answers},
            paired_ratio=statistics.median(x['samples_ns']['delivered']/x['samples_ns']['maintained'] for x in pairs),
            aa_ratio=statistics.median(a/b for a,b in aa))
        report['cases'].append(row)
        print(size,row['median_ms'],row['paired_ratio'],flush=True)
    (ROOT/'synthesis/data/cycle-block-prefix-benchmark.json').write_text(json.dumps(report,indent=2)+'\n')


if __name__=='__main__':main()
