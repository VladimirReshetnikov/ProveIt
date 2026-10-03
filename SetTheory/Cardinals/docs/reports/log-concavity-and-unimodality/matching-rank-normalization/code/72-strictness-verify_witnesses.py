"""Independent rank-two contraction witnesses via Boolean transversal matching.
No generic determinant or floating-point linear algebra is used.
"""
from itertools import combinations,product
from functools import lru_cache
from random import Random
from pathlib import Path
import json

@lru_cache(None)
def independent(rows):
 if not rows:return True
 row=min(rows,key=int.bit_count)
 if not row:return False
 rest=list(rows);rest.remove(row)
 while row:
  bit=row&-row;row-=bit
  if independent(tuple(sorted(r&~bit for r in rest))):return True
 return False

def witness(rows,nred,a,rank):
 reds=range(nred);blues=range(nred,len(rows));checked=0
 for ri in combinations(reds,a-1):
  for bi in combinations(blues,rank-a-1):
   I=ri+bi;ir=tuple(rows[i] for i in I);checked+=1
   if not independent(tuple(sorted(ir))):continue
   active=[i for i in range(len(rows)) if i not in I and independent(tuple(sorted(ir+(rows[i],))))]
   for u in active:
    opposite=[v for v in active if (v<nred)!=(u<nred)]
    if all(independent(tuple(sorted(ir+(rows[u],rows[v])))) for v in opposite):
     return {'I':I,'monochromatic_element':u,'color':'red' if u<nred else 'blue','subsets_checked':checked}
 return None

def graph(q,core,L,a,b,m):
 # a,b indicate presence, not numerical activities.
 red=[core[0]|1<<q,core[1]|1<<(q+1)]+L
 blue=[1<<j for j in range(q)]
 if b:blue.append(1<<q)
 if a:blue.append(1<<(q+1))
 blue += [3<<q]*m
 return red+blue,len(red)

rng=Random(771093);records=[];cases=0;gaps=0;stars=0
for q in range(6):
 cores=list(product(range(1<<q),repeat=2)) if q<=3 else [(rng.randrange(1<<q),rng.randrange(1<<q)) for _ in range(20)]
 for core in cores:
  for mode in range(3):
   L=[1<<j for j in range(q)]
   if mode!=0:L += [rng.randrange(1<<q) for _ in range(2)]
   a,b=(1,1) if mode==0 else (rng.randrange(2),rng.randrange(2))
   m=0 if mode==0 else rng.randrange(1,4)
   if a*b+(a+b)*m+m*(m-1)//2==0:a=1
   rows,nred=graph(q,core,L,a,b,m);rank=q+2
   structural_nonstar=bool(core[0] or core[1] or any(t.bit_count()>1 for t in L) or m)
   ws=[]
   for k in range(1,rank):
    w=witness(rows,nred,k,rank)
    assert bool(w)==structural_nonstar,(q,core,L,a,b,m,k,w)
    if w:
     ws.append({'index':k,**w});gaps+=1
   cases+=1;stars+=not structural_nonstar
   records.append({'q':q,'core':core,'L':L,'right_singleton_presence':[a,b],'common_count':m,'nonstar':structural_nonstar,'witnesses':ws})
report={'seed':771093,'graphs':cases,'q_values':list(range(6)),'strict_gap_witnesses':gaps,'star_graphs_without_monochromatic_witness':stars,'all_tests_passed':True,'oracle':'Exact Boolean transversal independence, then rank-two contraction parallel classes','records':records}
Path(__file__).with_name('witness_verification.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps({k:v for k,v in report.items() if k!='records'},indent=2))
