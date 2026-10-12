"""Pinned paired endpoint descent/replay and fresh-PD recognition measurements."""
import argparse
from hashlib import sha256
import json
from pathlib import Path
import platform
import random
import statistics
import subprocess
from time import perf_counter
import types
from unittest.mock import patch

from fastunknot import Diagram, recognize
from fastunknot.braid import braid_certificate
from fastunknot import braid_reduction

BASELINE='c4c23b61d844b465b9ee30d0cebb02af82050306'
ROOT=Path(__file__).resolve().parent
REPO=ROOT.parents[2]


def baseline(name):
    module=types.ModuleType(name)
    source=subprocess.check_output(['git','show',BASELINE+':Topology/UnknotRecognition/fast/fastunknot/braid_reduction.py'],cwd=REPO)
    exec(compile(source,name,'exec'),module.__dict__)
    return module


def cases():
    rows=[]
    for strands in (16,64,128,256,1024,4096):
        rows.append(dict(name=f'right-{strands}',kind='kernel',strands=strands,
                         word=[1,-2]+list(range(3,strands))))
        rows.append(dict(name=f'left-{strands}',kind='kernel',strands=strands,
                         word=[strands-2,-(strands-1)]*2+list(range(1,strands-2))))
    rows.append(dict(name='small-rank-stall',kind='kernel',strands=4,
                     word=[-3,-3,2,-3,2,1,1,1,-2,1,-2]*15))
    for strands in (16,128,512,2048):
        rows.append(dict(name=f'raw-recognition-{strands}',kind='braid',strands=strands,
                         word=[1,-2]+list(range(3,strands)),expected='UNKNOT'))
    for strands in (16,128,512):
        rows.append(dict(name=f'pd-recognition-{strands}',kind='pipeline',strands=strands,
                         word=[1,-2]+list(range(3,strands)),expected='UNKNOT'))
    return rows


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path,required=True)
    args=parser.parse_args()
    modules={'baseline':baseline('baseline'),'control':baseline('control'),'adaptive':braid_reduction}
    sources=[Path(__file__),*sorted((ROOT/'fastunknot').glob('*.py'))]
    hashes={str(p.relative_to(REPO)):sha256(p.read_bytes()).hexdigest() for p in sources}
    rng=random.Random(261008112);records=[]
    for case in cases():
        for round_number in range(6):
            order=list(modules);rng.shuffle(order)
            for arm in order:
                module=modules[arm];calls=[];producer=module.singleton_reduce
                def tracked(*a,**kw):
                    result=producer(*a,**kw);calls.append(result[2]);return result
                with patch('fastunknot.braid_reduction.singleton_reduce',tracked):
                    start=perf_counter()
                    if case['kind']=='kernel':
                        n,w,cert=tracked(case['strands'],case['word'])
                        assert module.verify_singleton_reduction(case['strands'],case['word'],cert)==(n,w)
                        status='COMPLETE';method='descent-and-replay'
                    elif case['kind']=='braid':
                        result=braid_certificate(case['strands'],case['word'],use_braid_reduction=True)
                        cert=result.get('strand_reduction')
                        if cert is not None:
                            module.verify_singleton_reduction(case['strands'],case['word'],cert)
                        status=result['status'];method=result['method']
                    else:
                        diagram=Diagram.from_braid(case['strands'],case['word'])
                        result=recognize(diagram,seconds=15,use_braid_reduction=True)
                        status=result.status;method=result.method
                    elapsed=perf_counter()-start
                if case['kind']!='kernel':assert status in (case['expected'],'UNKNOWN')
                records.append(dict(case=case['name'],kind=case['kind'],round=round_number,
                    warmup=round_number==0,arm=arm,arm_order=order,seconds=elapsed,status=status,
                    method=method,descent_calls=len(calls),
                    linear_calls=sum(c['kind']=='singleton-markov-descent-v2' for c in calls),
                    queue_pops=sum(c.get('queue_pops',0) for c in calls),
                    trace_records=sum(len(c['steps']) for c in calls)))
    summary=[]
    for case in cases():
        samples=[r for r in records if r['case']==case['name'] and not r['warmup']]
        medians={arm:statistics.median(r['seconds'] for r in samples if r['arm']==arm) for arm in modules}
        complete=all(r['status']!='UNKNOWN' for r in samples)
        ratios={arm:statistics.median(next(r['seconds'] for r in samples if r['arm']=='baseline' and r['round']==i)/
                next(r['seconds'] for r in samples if r['arm']==arm and r['round']==i)
                for i in range(1,6)) if complete else None for arm in ('control','adaptive')}
        summary.append(dict(case=case['name'],kind=case['kind'],median_seconds=medians,paired_ratios=ratios,
            complete=complete,adaptive_linear_calls=sum(r['linear_calls'] for r in samples if r['arm']=='adaptive')))
    for p in sources:assert sha256(p.read_bytes()).hexdigest()==hashes[str(p.relative_to(REPO))]
    result=dict(baseline_commit=BASELINE,seed=261008112,python=platform.python_version(),
        scope='Kernel times include generation and certificate replay; raw braid recognition adds source closure validation and replay; pipeline includes fresh PD construction and default recognition. Imports and JSON serialization excluded. Whole-pipeline shortcut activation reported separately.',
        source_sha256=hashes,cases=cases(),samples=records,summary=summary,
        measured=sum(not r['warmup'] for r in records),warmups=sum(r['warmup'] for r in records))
    args.output.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k not in ('cases','samples','source_sha256')},indent=2))

if __name__=='__main__':main()
