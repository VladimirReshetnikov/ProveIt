"""Matched exact-output component benchmark; archive code is never imported."""
import json,random,time,statistics,hashlib,sys
from pathlib import Path
from matching_factorized_before_sparse import solve
rng=random.Random(260327)
fixtures=[('tiny',[(0,0)],1),('tiny-q2',[(0,0)],2)]
for M,Q,L,R in [(16,2,6,6),(32,4,8,8),(64,8,12,12),(96,12,16,16),(128,16,20,20),(192,24,24,24)]:
    fixtures.append((f'random-M{M}-Q{Q}',[(rng.randrange(L),rng.randrange(R)) for _ in range(M)],Q))
fixtures.append(('parallel-M96-Q12',[(0,0)]*96,12))
fixtures.append(('single-matching-M96-Q12',[(i,i) for i in range(96)],12))
records=[]
for name,edges,Q in fixtures:
    expected=solve(edges,Q,4,'dense')
    if solve(edges,Q,4,'factorized')!=expected:raise ArithmeticError(name)
    raw={'dense':[],'factorized':[]}
    for rep in range(5):
        for method in (['dense','factorized'] if rep%2==0 else ['factorized','dense']):
            t=time.perf_counter();cpu=time.process_time();out=solve(edges,Q,4,method)
            elapsed=time.perf_counter()-t;cpuelapsed=time.process_time()-cpu
            if out!=expected:raise ArithmeticError((name,method,rep))
            raw[method].append({'wall':elapsed,'cpu':cpuelapsed})
    med={m:{k:statistics.median(x[k] for x in raw[m]) for k in ['wall','cpu']} for m in raw}
    records.append({'name':name,'edges':edges,'M':len(edges),'Q':Q,'eta':4,'matching_count':len(expected['groups']),
    'raw':raw,'median':med,'wall_speedup':med['dense']['wall']/med['factorized']['wall'],
    'cpu_speedup':med['dense']['cpu']/med['factorized']['cpu']})
print(json.dumps({'scope':'Synthetic component tests. Maintained dense O(MQ²+VQ) reference, not literal recomputation. All calls include matching/color initialization, exact candidate averaging checks, final outputs and selected trace. Shared environment, five alternating repetitions after equal-output warmup; no full SAT speedup claim.',
'implementation_sha256':hashlib.sha256(Path(__file__).with_name('matching_factorized_before_sparse.py').read_bytes()).hexdigest(),
'python':sys.version,'results':records},indent=2))
