"""Paired stage benchmarks; no claim about the full ProveIt pipeline."""
from __future__ import annotations
import json, platform, random, statistics, sys
from pathlib import Path
from time import perf_counter
sys.path.insert(0,str(Path(__file__).resolve().parents[1]))
from braidkernel import Braid, kernelize, recognize
from braidkernel.descent import linear_descent, verify_descent
from braidkernel.cube import reduced_khovanov
from upstream_endpoint_baseline import singleton_reduce

ROOT=Path(__file__).resolve().parents[1]
rng=random.Random(20261008)

def timed(fn):
    t=perf_counter(); answer=fn(); return perf_counter()-t,answer

def checked_descent(x):
    y,c=linear_descent(x)
    assert verify_descent(x,c)==y
    return y

out={'scope':'source-derived endpoint helper and standalone cube pipeline, not upstream full pipeline',
     'platform':platform.platform(),'python':sys.version,'seed':20261008,
     'rounds':5,'endpoint':[],'controls':[],'standalone_recognition':[]}
for b in [64,256,1024,4096]:
    x=Braid.checked(b,[1,2,1,-2]+list(range(3,b)))
    samples=[]
    arms={'baseline':lambda:singleton_reduce(x.strands,x.word),
          'control':lambda:singleton_reduce(x.strands,x.word),
          'new_verified':lambda:checked_descent(x)}
    for repeat in range(5):
        keys=list(arms);rng.shuffle(keys);record={}
        for name in keys:
            elapsed,answer=timed(arms[name]);record[name]=elapsed
            if name=='new_verified':assert answer==Braid.checked(3,[1,2,1,-2])
            else:assert answer[:2]==(3,(1,2,1,-2))
        samples.append(record)
    row={'strands':b,'letters':len(x.word),'samples':samples,
         'median_baseline_seconds':statistics.median(r['baseline'] for r in samples),
         'median_new_verified_seconds':statistics.median(r['new_verified'] for r in samples),
         'median_paired_speedup':statistics.median(r['baseline']/r['new_verified'] for r in samples),
         'median_AA':statistics.median(r['baseline']/r['control'] for r in samples)}
    out['endpoint'].append(row); print('endpoint',b,row['median_paired_speedup'],flush=True)
for name,x in [('no-cut-core',Braid.checked(3,[1,2,1,-2])),
               ('internal-only',Braid.checked(4,[1,1,1,-3,-3,-3,2]))]:
    samples=[]
    for repeat in range(15):
        keys=['baseline','new_verified'];rng.shuffle(keys);record={}
        for key in keys:
            fn=(lambda:singleton_reduce(x.strands,x.word)) if key=='baseline' else (lambda:checked_descent(x))
            # Batches resolve tiny-function timings; each call builds fresh work arrays.
            elapsed,_=timed(lambda:[fn() for _ in range(50)])
            record[key]=elapsed/50
        samples.append(record)
    out['controls'].append({'name':name,'samples':samples,
       'median_paired_speedup':statistics.median(r['baseline']/r['new_verified'] for r in samples)})
for b in [5,7,9]:
    x=Braid.checked(b,[1,2,1,-2]+list(range(3,b)))
    samples=[]
    for repeat in range(3):
        keys=['raw_cube','kernel_cube'];rng.shuffle(keys);record={}
        for key in keys:
            fn=(lambda:reduced_khovanov(x,max_generators=None)) if key=='raw_cube' else (lambda:recognize(x))
            elapsed,answer=timed(fn);record[key]=elapsed
            assert answer.get('reduced_rank',1)==1 and answer.get('status','UNKNOT')=='UNKNOT'
        samples.append(record)
    raw=reduced_khovanov(x,max_generators=None)
    out['standalone_recognition'].append({'strands':b,'letters':len(x.word),'samples':samples,
       'raw_generators':raw['enhanced_generators'],
       'median_paired_speedup':statistics.median(r['raw_cube']/r['kernel_cube'] for r in samples)})
(ROOT/'data/benchmark.json').write_text(json.dumps(out,indent=2)+'\n')
print('controls',[(r['name'],r['median_paired_speedup']) for r in out['controls']])
print('standalone',[(r['letters'],r['median_paired_speedup'],r['raw_generators']) for r in out['standalone_recognition']])
