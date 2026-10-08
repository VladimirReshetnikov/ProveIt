"""Exhaustive short three-braids and planted internal-cut validation."""
from __future__ import annotations
import itertools,json,random,sys,platform
from pathlib import Path
from time import perf_counter
sys.path.insert(0,str(Path(__file__).resolve().parents[1]))
from braidkernel import Braid,kernelize,singleton_certificate,verify_certificate,connected_sum_braid
from braidkernel.cube import reduced_khovanov,normalized_bracket
from braidkernel.descent import linear_descent,verify_descent
from upstream_endpoint_baseline import singleton_reduce
ROOT=Path(__file__).resolve().parents[1]

def b3_matrix_verdict(x):
    # Independent source-documented three-braid characterization; not a new theorem.
    a,b,c,d=1,0,0,1
    for g in x.word:
        if g==1:b,d=a+b,c+d
        elif g==-1:b,d=b-a,d-c
        elif g==2:a,c=a-b,c-d
        elif g==-2:a,c=a+b,c+d
    return abs(x.exponent)<=2 and abs(2-a-d)==1

start=perf_counter(); records=[]; candidates=0
for n in [2,4,6]:
    for w in itertools.product((-2,-1,1,2),repeat=n):
        candidates+=1
        try:x=Braid.checked(3,w)
        except ValueError:continue
        h=reduced_khovanov(x,check_d_squared=True)
        result=kernelize(x)
        assert b3_matrix_verdict(x)==(h['reduced_rank']==1)
        if result['status']=='KNOTTED':assert h['reduced_rank']>1
        if result['status']=='UNKNOT':assert h['reduced_rank']==1
        fs=verify_certificate(x,result['certificate'])
        product=1
        for f in fs:product*=reduced_khovanov(f)['reduced_rank']
        assert product==h['reduced_rank']
        records.append({'strands':3,'word':w,'reduced_rank':h['reduced_rank'],
                        'kernel_status':result['status'],'core_letters':result['stats']['core_letters']})
print('exhaustive',len(records),'of',candidates,'seconds',perf_counter()-start,flush=True)
rng=random.Random(408513);planted=[]
seeds=[(1,2,1,-2),(1,-2,1,-2),(-1,-2,-1,2)]
for j in range(32):
    left=list(rng.choice(seeds));right=[(1 if g>0 else -1)*(abs(g)+3) for g in rng.choice(seeds)]
    word=[]
    while left or right:
        take=left if left and (not right or rng.randrange(2)) else right
        word.append(take.pop(0))
    word.insert(rng.randrange(9),rng.choice((-3,3)))
    x=Braid.checked(6,word);fs=verify_certificate(x,singleton_certificate(x));merged=connected_sum_braid(fs)
    h=reduced_khovanov(x,check_d_squared=True)
    product=1
    for f in fs:product*=reduced_khovanov(f)['reduced_rank']
    assert h['reduced_rank']==product==reduced_khovanov(merged)['reduced_rank']
    assert normalized_bracket(x)==normalized_bracket(merged)
    planted.append({'word':word,'reduced_rank':product,'merged':merged.to_json()})
compared=0
while compared<1000:
    b=rng.randint(2,10);n=rng.randint(b-1,60)
    w=[rng.choice((-1,1))*rng.randrange(1,b) for _ in range(n)]
    try:x=Braid.checked(b,w)
    except ValueError:continue
    y,c=linear_descent(x);assert verify_descent(x,c)==y
    ob,ow,_=singleton_reduce(b,w)
    assert ob==y.strands
    assert len(ow)==len(y.word)
    assert not ow or any(y.word==ow[j:]+ow[:j] for j in range(len(ow)))
    assert c['queue_pops']<=2*len(w)
    compared+=1
summary={'python':platform.python_version(),'candidate_three_braids':candidates,
         'exhaustive_knot_closures':len(records),'planted_internal_cut_cases':len(planted),
         'd_squared_checked_originals':len(records)+len(planted),
         'random_endpoint_baseline_comparisons':compared,'mismatches':0,
         'seconds':perf_counter()-start,'seed':408513,
         'scope':'finite validation, not formal verification or full upstream regression'}
(ROOT/'data/validation_summary.json').write_text(json.dumps(summary,indent=2)+'\n')
(ROOT/'data/validation_cases.json').write_text(json.dumps({'three_braids':records,'planted':planted},indent=2)+'\n')
print(json.dumps(summary,indent=2))
