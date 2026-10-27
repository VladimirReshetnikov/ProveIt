"""Independent component audit. Imports only new authored kernel modules.

No incoming archive code is executed. All checks are explicit under python -O.
"""
from fractions import Fraction as F
from itertools import product
from pathlib import Path
import sys, json, random, hashlib
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'code'))
from sparse_balancing import balance
from cauchy_kernel import Parameters, Ring, product_tables, recurrent_tables, Prepared

counts = {}
def require(ok, description):
    if not ok: raise ArithmeticError(description)
def bump(key, n=1): counts[key] = counts.get(key, 0) + n

def packing_direct(adj, Q, h):
    n = len(adj[0]) if adj else 0
    totals = [0]*Q; rows = []
    for row in adj:
        a = min(range(Q), key=lambda x:(totals[x], x))
        rows.append(a); totals[a] += sum(row)
    C = max((sum(row[j] for row in adj) for j in range(n)), default=0)
    q = F(h*max(1,C)+1, h*max(1,C))
    prefix=[]; all_scores=[]
    for j in range(n):
        scores=[]
        for candidate in range(Q):
            score=F(0)
            for tail in product(range(Q), repeat=n-j-1):
                cols=prefix+[candidate]+list(tail)
                cells=[[0]*Q for _ in range(Q)]
                for i,row in enumerate(adj):
                    for k,w in enumerate(row): cells[rows[i]][cols[k]] += w
                score += sum((q**cell for row in cells for cell in row), F(0))
            scores.append(score / Q**(n-j-1))
        prefix.append(min(range(Q), key=lambda x:(scores[x],x)))
        all_scores.append(scores)
    return rows,prefix,all_scores

fixtures=[[], [[],[]], [[0,0,0]], [[1]*9], [[0,2,0,0],[3,0,0,0]], [[17,0,2],[0,1,0]]]
fixtures += [[[v[0],v[1],v[2]],[v[3],v[4],v[5]]] for v in product(range(2),repeat=6)]
rng=random.Random(10272026)
fixtures += [[[rng.randrange(4) if rng.random()<.45 else 0 for j in range(4)] for i in range(4)] for _ in range(25)]
for index,adj in enumerate(fixtures):
    for Q in (1,2,3,6):
        for h in (2,11):
            outputs=[balance(adj,Q,h,m,certificate=True) for m in ('cubic','dense','sparse')]
            for key in ('row_labels','column_labels','loads','initial','final','steps'):
                require(all(o[key]==outputs[0][key] for o in outputs), f'packing {index} Q={Q} h={h}: {key}')
            require(outputs[2]['stats']['score_terms']<=outputs[1]['stats']['score_terms'],'sparsity count')
            bump('three_method_packing_configurations')
            for method,reference in zip(('cubic','dense','sparse'),outputs):
                timed=balance(adj,Q,h,method,certificate=True,checks=False,count=False)
                for key in ('row_labels','column_labels','loads','initial','final','steps'):
                    require(timed[key]==reference[key],'counter/check toggle changed output')
                require(all(timed['stats'][key]==0 for key in ('score_terms','score_multiplications','active_row_updates','candidate_scans')),'disabled counter not zero')
                bump('unchecked_uncounted_equivalence_controls')
            if index != 3 and Q in (1,2,3) and (index<8 or index%11==0):
                rows,cols,scores=packing_direct(adj,Q,h)
                out=outputs[-1]
                require(out['row_labels']==rows and out['column_labels']==cols,'brute labels')
                require([s['scores'] for s in out['steps']]==scores,'brute conditional potential')
                bump('packing_direct_completion_configurations')
                bump('packing_direct_completion_steps',len(scores))
require(balance([[1]*9],4,2)['column_labels']==[0,1,2,3,0,1,2,3,0],'tie/absent-zero selection')
bump('packing_tie_cycle_controls')
for adj in ([],[[],[]],[[0]*12 for _ in range(7)]):
    out=balance(adj,9,3)
    require(out['initial']==81 and out['final']==81,'empty potential')
    require(all(b==0 for b in out['column_labels']),'empty column label')
    bump('packing_empty_zero_controls')

# Exact arithmetic in Q[U]/(U^2+U+1), with no kernel helper imports.
def mul(x,y):
    a,b=x; c,d=y
    return a*c-b*d, a*d+b*c-b*d
def div(x,y):
    c,d=y; norm=c*c-c*d+d*d
    return mul(x,((c-d)/norm,-d/norm))
def scale(x,s):return x[0]*s,x[1]*s
def red(x,p):
    m=1<<p
    for c in x:require(c.denominator&1,'nonintegral oracle coefficient')
    return tuple(c.numerator*pow(c.denominator,-1,m)%m for c in x)
def v2(n):
    require(n!=0,'valuation oracle zero')
    a=0
    while n%2==0:n//=2;a+=1
    return a

def exact_tables(a,i,t,zeta):
    L=1<<a;R=1<<i;N=L//2
    slots=[x for x in range(L) if (x//R)%2==0]
    T=F(t+2*L*zeta[0]),F(2*L*zeta[1])
    pref=(F(1),F(0))
    for q in range(-L,L):
        if q:pref=mul(pref,scale((T[0]-q,T[1]),F(-1,q)))
    tables=[[],[]]
    for side in (0,1):
        for b,pivot in enumerate(slots):
            E=2*(b//R)-(b//R).bit_count()
            row=[]
            for x in slots:
                d=(x-pivot)*(1 if side==0 else -1)
                feature=div(T,(T[0]+d,T[1]))
                for previous in slots[:b]:
                    d=(x-previous)*(1 if side==0 else -1)
                    feature=div(scale(feature,d),(T[0]+d,T[1]))
                row.append(scale(mul(pref,feature),1<<E) if side==0 else scale(feature,F(1,1<<E)))
            tables[side].append(row)
    for j,x in enumerate(slots):
        for k,y in enumerate(slots):
            reconstructed=[F(0),F(0)]
            for b in range(N):
                term=mul(tables[0][b][j],tables[1][b][k])
                reconstructed=[reconstructed[h]+term[h] for h in (0,1)]
            require(tuple(reconstructed)==div(mul(pref,T),(T[0]+x-y,T[1])),'exact Cauchy reconstruction')
            bump('exact_cauchy_reconstructions')
    return tables

for a in range(1,5):
    L=1<<a
    for t in range(-L,L):
        if not t:continue
        i=v2(t)
        if i>=a:continue
        for zeta in ((0,0),(0,1),(1,1),(-2,3),(3,-4)):
            exact=exact_tables(a,i,t,zeta);N=L//2
            bump('all_grid_exact_cauchy_configurations')
            for p in (1,3,9,17):
                params=Parameters(a,i,t,zeta,p)
                old,new=product_tables(params),recurrent_tables(params)
                for side,key in enumerate(('target','source')):
                    expected=[[red(x,p) for x in row] for row in exact[side]]
                    require(old[key]==new[key]==expected,'Cauchy table exact mismatch')
                    bump('modular_cauchy_feature_equalities',N*N)
                if zeta==(0,0):
                    require(all(x==(0,0) for row in new['target'] for x in row),'zero target')
                    bump('zero_prefactor_controls')
                # All supported entries are O(N^2), initialization excludes output.
                init=new['counts']['initialization_multiplications']
                require(new['counts']['ring_multiplications']==init+2*N*N+N*(N+1)//2,'recurrence count')
                require(old['counts']['ring_multiplications']==init+N*(N+1)*(2*N+1)//3+N*(N+1)//2,'product count')
                bump('operation_count_controls',2)
                bump('all_grid_modular_cauchy_configurations')

for p in (1,2,5,11):
    ring=Ring(p);mod=1<<p
    vals=[(a,b) for a in range(-4,5) for b in range(-4,5) if (a&1) or (b&1)]
    inverses=ring.batch_inverse(vals)
    require(ring.inversions==1,'batch not one inverse')
    for x,y in zip(vals,inverses):
        require(ring.mul(x,y)==(1,0),'unit inverse')
        bump('extension_unit_inverse_controls')
    require(ring.batch_inverse([])==[],'empty batch')
    for x in ((0,0),(2,0),(0,2),(2,2)):
        try:ring.inverse(x)
        except ValueError:bump('nonunit_rejections')
        else:raise ArithmeticError('nonunit accepted')

root=Path(__file__).resolve().parents[1]
benchmarks={}
for name in ('balancing_benchmark','cauchy_benchmark'):
    path=root/'results'/f'{name}.json'
    data=json.loads(path.read_text()); records=data['records']
    if name=='balancing_benchmark':
        for rec in records:
            for method,samples in rec['seconds'].items():
                require(len(samples)==data['repetitions'] and min(samples)>0,'packing timing samples')
                require(sorted(samples)[len(samples)//2]==rec['medians'][method],'packing median')
                if 'cpu_seconds' in rec:
                    cpu=rec['cpu_seconds'][method]
                    require(len(cpu)==data['repetitions'] and min(cpu)>0,'packing CPU timing samples')
                    require(sorted(cpu)[len(cpu)//2]==rec['cpu_medians'][method],'packing CPU median')
            require(abs(rec['cubic_over_sparse']-rec['medians']['cubic']/rec['medians']['sparse'])<1e-12,'packing speed ratio')
        benchmarks[name]={'records':len(records),'cubic_over_sparse_range':[min(r['cubic_over_sparse'] for r in records),max(r['cubic_over_sparse'] for r in records)],'dense_over_sparse_range':[min(r['dense_over_sparse'] for r in records),max(r['dense_over_sparse'] for r in records)]}
    else:
        for rec in records:
            for method in ('product','recurrent'):
                samples=rec[f'{method}_samples_seconds']
                require(len(samples)==rec['repeats'] and min(samples)>0,'Cauchy timing samples')
                require(sorted(samples)[len(samples)//2]==rec[f'{method}_median_seconds'],'Cauchy median')
                if f'{method}_cpu_samples_seconds' in rec:
                    cpu=rec[f'{method}_cpu_samples_seconds']
                    require(len(cpu)==rec['repeats'] and min(cpu)>0,'Cauchy CPU samples')
                    require(sorted(cpu)[len(cpu)//2]==rec[f'{method}_median_cpu_seconds'],'Cauchy CPU median')
            require(abs(rec['measured_speedup']-rec['product_median_seconds']/rec['recurrent_median_seconds'])<1e-12,'Cauchy speed ratio')
        benchmarks[name]={'records':len(records),'measured_speedup_range':[min(r['measured_speedup'] for r in records),max(r['measured_speedup'] for r in records)]}
    benchmarks[name]['sha256']=hashlib.sha256(path.read_bytes()).hexdigest()
    benchmarks[name]['repeats']=sorted({r.get('repeats',data.get('repetitions')) for r in records})
    bump('benchmark_records_validated',len(records))

hashes={p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted((root/'code').glob('*.py'))}
result={'status':'PASS','python':sys.version,'optimization':sys.flags.optimize,'counts':counts,'benchmark_consistency':benchmarks,'audited_source_sha256':hashes,'scope':'Independent finite component audit only, not full SAT or general extension-degree certification. No incoming program imported or executed.'}
path=Path(sys.argv[1]) if len(sys.argv)>1 else root/'qa'/('performance_audit_checks_optimized.json' if sys.flags.optimize else 'performance_audit_checks_normal.json')
path.write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
