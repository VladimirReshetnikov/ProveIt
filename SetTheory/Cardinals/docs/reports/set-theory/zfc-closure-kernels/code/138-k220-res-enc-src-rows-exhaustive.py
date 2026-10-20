#!/usr/bin/env python3
"""Exhaust all 6^8 fixed-shape logical-row parameter permutations.

Count union masks for precomputed row fragments.  A cross-boundary node
whose leaf count occurs nowhere else is always distinct, so only the few
remaining cross-boundary nodes require explicit interning.  The reduction
is checked against the ordinary exact DAG counter on all individual
changes and 1000 seeded random joint changes.
"""
import itertools,json,random,time,collections
from functools import cache
import joint_sweep as j

@cache
def length(k):
    n=j.NODES[k]
    return 1 if isinstance(n[0],str)else sum(length(x)for x in n)

@cache
def bits(k):
    n=j.NODES[k]
    return(1<<k)if isinstance(n[0],str)else(1<<k)|bits(n[0])|bits(n[1])

def dependencies(sk):
    if sk[0]=='F':return set()
    if sk[0]=='R':return {sk[1]}
    return dependencies(sk[1])|dependencies(sk[2])

def prepare():
    baselengths=collections.Counter(length(k)for k in range(len(j.BASE_NODES)))
    mids=[];rowbits=[[0]*6 for _ in range(8)];fixed=0
    def visit(sk):
        nonlocal fixed
        if sk[0]=='F':fixed|=bits(sk[1]);return length(sk[1])
        if sk[0]=='R':
            for p,k in enumerate(sk[2]):rowbits[sk[1]][p]|=bits(k)
            return length(sk[2][0])
        size=visit(sk[1])+visit(sk[2]);mids.append((size,sk));return size
    visit(j.SKEL)
    midlengths=collections.Counter(n for n,_ in mids)
    critical=[];constant=0
    for size,sk in mids:
        if midlengths[size]==1 and baselengths[size]==0:
            constant+=1;continue
        deps=sorted(dependencies(sk));table={}
        for vals in itertools.product(range(6),repeat=len(deps)):
            v=[0]*8
            for r,p in zip(deps,vals):v[r]=p
            table[vals]=1<<j.getroot(sk,v)
        critical.append((deps,table))
    return fixed,rowbits,constant,critical

FIXED,ROWBITS,CONSTANT,CRITICAL=prepare()

def count(v):
    mask=FIXED
    for r,p in enumerate(v):mask|=ROWBITS[r][p]
    for deps,tab in CRITICAL:mask|=tab[tuple(v[r]for r in deps)]
    return CONSTANT+mask.bit_count()

def main():
    print('reduction',{'constant_unique_nodes':CONSTANT,'critical_nodes':len(CRITICAL),
                      'critical_parameter_counts':[len(d)for d,t in CRITICAL]},flush=True)
    rng=random.Random(20261020)
    validation=[tuple(rng.randrange(6)for _ in range(8))for _ in range(1000)]
    for i in range(8):
        for p in range(6):
            v=[0]*8;v[i]=p;validation.append(tuple(v))
    for v in validation:assert count(v)==j.count(v),(v,count(v),j.count(v))
    print('validated',len(validation),flush=True)
    best=999;solutions=[];hist=collections.Counter();started=time.monotonic()
    for k,v in enumerate(itertools.product(range(6),repeat=8)):
        n=count(v);hist[n]+=1
        if n<best:best=n;solutions=[];print('best',n,v,flush=True)
        if n==best:solutions.append(v)
        if k and k%200000==0:print('progress',k,'seconds',time.monotonic()-started,flush=True)
    report={'status':'EXHAUSTIVE_FIXED_SHAPE_ROW_PERMUTATION_DAG_COUNT_COMPLETE',
            'variants':6**8,'minimum_dag_nodes':best,'minimizers':solutions,
            'histogram':dict(sorted(hist.items())),'seconds':time.monotonic()-started,
            'constant_unique_cross_nodes':CONSTANT,'critical_cross_nodes':len(CRITICAL),
            'counter_validation_cases':len(validation)}
    (j.z.HERE/'exhaustive_summary.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report),flush=True)

if __name__=='__main__':main()
