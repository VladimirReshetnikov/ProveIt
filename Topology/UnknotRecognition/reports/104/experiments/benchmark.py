"""Controlled matrix-stage benchmarks, NOT whole-knot or geometry timings."""
import gc
import json
import platform
import statistics
import sys
import time
from pathlib import Path
from private_cocore import *
from reference import dense_saturated


def case(kind, m, q):
    if kind == 'chain':
        n = m + q + 1
        real = [{i:1, i+1:2 if i < m-1 else 1} for i in range(m)]
        passive = [{0:1, m+1+i:1} for i in range(q)]
    elif kind == 'dense':
        n = m + q
        real = [{i:1, **{h:1 for h in range(i+1,n)}} for i in range(m)]
        passive = [{h:1 for h in range(n) if (h+i)%3} for i in range(q)]
    else:
        n = m+q
        real = [{i:1, m+(i%q):1} for i in range(m)]
        passive = [{i:1} for i in range(q)]
    return real, n, passive, [(i,i) for i in range(m)]


def timed(f, repeats=7):
    values = []
    for _ in range(repeats):
        gc.collect()
        t = time.perf_counter(); f(); values.append(time.perf_counter()-t)
    return {'median_seconds':statistics.median(values), 'samples_seconds':values}

records=[]
for kind,m,q in [('tiny',1,1),('tiny',2,2),('chain',16,16),('chain',48,48),('chain',96,96),('dense',24,48)]:
    a,n,b,s=case(kind,m,q)
    expected=dense_saturated(a,n,b,s)
    c=produce_certificate(a,n,b,s)
    assert tuple(c['least_private'])==expected
    assert verify_certificate(a,n,b,c)
    baseline=timed(lambda:dense_saturated(a,n,b,s))
    production=timed(lambda:produce_certificate(a,n,b,s))
    replay=timed(lambda:verify_certificate(a,n,b,c))
    def combined():
        cert=produce_certificate(a,n,b,s)
        assert verify_certificate(a,n,b,cert)
    certified=timed(combined)
    record={'family':kind,'m':m,'n':n,'q':q,'s':sum(map(len,a)), 'z':sum(map(len,b)),
            'dense_query':baseline,'owner_producer':production,'independent_replay':replay,
            'producer_plus_replay':certified,
            'dense_over_owner':baseline['median_seconds']/production['median_seconds'],
            'dense_over_certified':baseline['median_seconds']/certified['median_seconds']}
    records.append(record)
    print(kind,m,q,round(record['dense_over_owner'],2),round(record['dense_over_certified'],2))
result={'scope':'Synthetic matrix stage only; source geometry and whole recognizer excluded.',
        'python':sys.version,'platform':platform.platform(),'repeats':7,'records':records}
Path('data/benchmarks.json').write_text(json.dumps(result,indent=2)+'\n')

# Scalar/atlas fixture and complete bounded-exception search.
b=[{0:1},{0:1,1:1},{1:1,2:1},{2:1}]
p=compile_program([],3,[])
answers=[]
for k in range(3):
    a=build_atlas(p,b,k); answers.append({'k':k,**find_exceptions(a)})
Path('data/exception-example.json').write_text(json.dumps(answers,indent=2)+'\n')
# Saved independent certificate fixture, with explicit source.
real,n,passive,schedule=case('chain',8,8)
c=produce_certificate(real,n,passive,schedule)
Path('data/certificate-example.json').write_text(json.dumps({'real':real,'n_columns':n,'passive':passive,'certificate':c},indent=2)+'\n')
