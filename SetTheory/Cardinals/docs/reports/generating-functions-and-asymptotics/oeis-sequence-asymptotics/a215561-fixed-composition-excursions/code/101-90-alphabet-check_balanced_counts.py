"""Direct content-vector DP checks of the general family normalization."""
from itertools import product
from math import factorial,comb
from pathlib import Path
import json,time
start=time.time();records=[]
known={4:[1,7,403,40350,5223915,783353872],5:[1,35,18720,19369350,27032968200,44776592395920],6:[1,139,746192,9212531290],7:[1,1001,71892912]}
for r,cap in [(2,30),(3,20),(4,16),(5,9),(6,7),(7,5)]:
    steps=list(range(-(r-1),r,2)) if r%2==0 else list(range(-(r//2),r//2+1))
    D={(0,)*r:1}
    for v in product(range(cap+1),repeat=r):
        if not any(v) or sum(x*j for x,j in zip(v,steps))<0:continue
        value=0
        for j,x in enumerate(v):
            if x:
                prev=list(v);prev[j]-=1;value+=D.get(tuple(prev),0)
        if value:D[v]=value
    diag=[D[(n,)*r] for n in range(cap+1)]
    if r in known and diag[:len(known[r])]!=known[r]:raise RuntimeError(('OEIS initial terms',r))
    if r==2 and any(v!=comb(2*n,n)//(n+1) for n,v in enumerate(diag)):raise RuntimeError('Catalan')
    if r==3 and any(v!=factorial(3*n)//factorial(n)**3//(n+1) for n,v in enumerate(diag)):raise RuntimeError('Motzkin content')
    n=cap;bridge=factorial(r*n)//factorial(n)**r
    records.append({'r':r,'maximum_n':cap,'nonzero_DP_states':len(D),'diagonal':diag,'critical_value_estimate_rn_times_ratio':r*n*diag[-1]/bridge})
    print('passed',r,cap,len(D),flush=True)
out={'exact_checks_passed':True,'records':records,'seconds':time.time()-start,'scope':'Exact finite definitions and normalizations; the critical-value estimates are supplementary numerical orientation'}
Path(__file__).with_suffix('.json').write_text(json.dumps(out,indent=2)+'\n')
