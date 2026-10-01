"""Exact finite derivative-support regression; not a proof of asymptotics."""
import json
from pathlib import Path
from time import perf_counter
def require(condition,message):
 if not condition:raise RuntimeError(message)

P={(0,0):1};rows=[];start=perf_counter()
for N in range(1,201):
 Q={}
 for (j,k),c in P.items():
  for key,v in (((j+1,k),c),((j+1,k+1),2*c),((j-1,k),j*c)):
   Q[key]=Q.get(key,0)+v
  if k:
   key=(j-1,k-1);Q[key]=Q.get(key,0)+k*c
 P={key:v for key,v in Q.items() if v}
 require(all((N+j)%2==0 and 0<=k<=(N+j)//2<=N for j,k in P),f"Support envelope at N={N}")
 bulk=(3*N*N+10*N+8)//8 if N%2==0 else (3*N*N+12*N+1)//8
 require(sum(j>=0 or j==-1 for j,k in P)==bulk,f"Bulk count at N={N}")
 tail_candidates=[];unexpected=[];forced=[]
 for d in range(1,N//2+1):
  for k in range((N-2)//2-d+1):
   q=N-2*k-2*d-1
   require(q>=1,f"Tail index at N={N}")
   key=(-q-1,k)
   isforced=q==2*d and (k+d)%2==0
   if isforced:
    require(key not in P,f"Reflection hole at N={N}");forced.append(key)
   elif key not in P:unexpected.append((d,k,q))
   tail_candidates.append(key)
 require(len(P)==bulk+len(tail_candidates)-len(forced)-len(unexpected),f"Complete count at N={N}")
 rows.append(dict(N=N,a_N=len(P),bulk=bulk,tail_candidates=len(tail_candidates),forced_holes=len(forced),unexpected_cancellations=len(unexpected),ratio=len(P)/(N*N)))
 if N in [10,20,50,100,150,200]:print(rows[-1],flush=True)
 if unexpected:print('Unexpected zeros',N,unexpected[:20],flush=True)
Path(__file__).with_name('derivative_counts.json').write_text(json.dumps(dict(scope='Finite exact regression only; does not prove the noncancellation conjecture or asymptotic theorem',rows=rows,seconds=perf_counter()-start),indent=2))
print('complete',perf_counter()-start,flush=True)
