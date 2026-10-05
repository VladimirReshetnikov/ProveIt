"""Direct balanced basketball DP, independent of the conjectured recurrence."""
from itertools import product
from math import comb
from pathlib import Path
import json,time,sys
ROOT=Path(__file__).resolve().parent;cap=int(sys.argv[1]) if len(sys.argv)>1 else 25;start=time.time();steps=(-2,-1,1,2);D={(0,0,0,0):1}
# Lexicographic order suffices, since removing any step lowers one coordinate.
for v in product(range(cap+1),repeat=4):
 if not any(v):continue
 if sum(x*y for x,y in zip(v,steps))<0:continue
 val=0
 for j in range(4):
  if v[j]:
   w=list(v);w[j]-=1;val+=D.get(tuple(w),0)
 if val:D[v]=val
B=[D.get((n,)*4,0) for n in range(cap+1)];A=[comb(5*n,n)*v for n,v in enumerate(B)]
expected=[1,35,18720,19369350,27032968200,44776592395920,82881380383401600,165850226337286576800,351597937025844947295000,779279938350147159519336600,1789294251011628021153241548800,4228135363283244543270651711564000,10232120200642411474243152429724152000]
if A[:len(expected)]!=expected[:len(A)]:raise RuntimeError('OEIS initial values disagree')
out={'all_pass':True,'maximum_n':cap,'DP_states':len(D),'seconds':time.time()-start,'basketball':B,'A215570':A};(ROOT/'direct_terms.json').write_text(json.dumps(out,indent=2)+'\n');print('PASS',cap,len(D),time.time()-start)
