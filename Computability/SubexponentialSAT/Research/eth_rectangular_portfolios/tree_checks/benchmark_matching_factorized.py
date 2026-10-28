"""Matched exact-output component benchmark; archive code is never imported."""
import json,random,time,statistics,hashlib,sys
from pathlib import Path
from matching_factorized import solve
implementation_path=Path(__file__).with_name('matching_factorized.py')
implementation_sha256=hashlib.sha256(implementation_path.read_bytes()).hexdigest()
benchmark_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
rng=random.Random(260327)
fixtures=[('tiny',[(0,0)],1),('tiny-q2',[(0,0)],2)]
for M,Q,L,R in [(16,2,6,6),(32,4,8,8),(64,8,12,12),(96,12,16,16),(128,16,20,20),(192,24,24,24)]:
    fixtures.append((f'random-M{M}-Q{Q}',[(rng.randrange(L),rng.randrange(R)) for _ in range(M)],Q))
fixtures.append(('parallel-M96-Q12',[(0,0)]*96,12))
fixtures.append(('single-matching-M96-Q12',[(i,i) for i in range(96)],12))
fixtures.append(('filled-single-matching-M256-Q8',[(i,i) for i in range(256)],8))
records=[]
for name,edges,Q in fixtures:
    expected=solve(edges,Q,4,'dense')
    if name.startswith('filled-') and (len(expected['groups'])!=1 or sum(v>0 for row in expected['loads'] for v in row)!=Q*Q):raise ArithmeticError('filled control did not fill all cells')
    if any(solve(edges,Q,4,m)!=expected for m in ['factorized','sparse']):raise ArithmeticError(name)
    raw={'dense':[],'factorized':[],'sparse':[]}
    for rep in range(5):
        methods=['dense','factorized','sparse']; methods=methods[rep%3:]+methods[:rep%3]
        if rep%2:methods.reverse()
        for method in methods:
            t=time.perf_counter();cpu=time.process_time();out=solve(edges,Q,4,method)
            elapsed=time.perf_counter()-t;cpuelapsed=time.process_time()-cpu
            if out!=expected:raise ArithmeticError((name,method,rep))
            raw[method].append({'wall':elapsed,'cpu':cpuelapsed})
    med={m:{k:statistics.median(x[k] for x in raw[m]) for k in ['wall','cpu']} for m in raw}
    records.append({'name':name,'edges':edges,'M':len(edges),'Q':Q,'eta':4,'matching_count':len(expected['groups']),'positive_output_cells':sum(v>0 for row in expected['loads'] for v in row),
    'raw':raw,'median':med,'wall_speedup':med['dense']['wall']/med['factorized']['wall'],
    'cpu_speedup':med['dense']['cpu']/med['factorized']['cpu'],
    'dense_over_sparse_wall':med['dense']['wall']/med['sparse']['wall'],
    'dense_over_sparse_cpu':med['dense']['cpu']/med['sparse']['cpu'],
    'factorized_over_sparse_wall':med['factorized']['wall']/med['sparse']['wall'],
    'factorized_over_sparse_cpu':med['factorized']['cpu']/med['sparse']['cpu']})
if hashlib.sha256(implementation_path.read_bytes()).hexdigest()!=implementation_sha256:raise ArithmeticError('implementation changed during benchmark')
if hashlib.sha256(Path(__file__).read_bytes()).hexdigest()!=benchmark_sha256:raise ArithmeticError('benchmark changed during run')
print(json.dumps({'scope':'Synthetic component tests. Maintained dense O(MQ²+VQ) reference, not literal recomputation. All three methods include matching/color initialization, final dense load output and selected trace; implementation invariant checks are included. Sparse averaging is symbolic and deliberately avoids unrequested full candidate materialization (tested separately). Shared environment, five alternating/rotating repetitions after equal-output warmup; no full SAT speedup claim.',
'implementation_sha256':implementation_sha256,'benchmark_sha256':benchmark_sha256,'start_end_hashes_agree':True,
'python':sys.version,'results':records},indent=2))
