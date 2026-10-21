from pathlib import Path
import sys,json,time
BASE=Path('/workspace/scratch/1d1a80d76be0/ProveIt/Computability/BusyBeaver/Research/ZFC/candidate-k215')
sys.path.insert(0,str(BASE/'code/runtime-inputs/runtime'));import independent_runtime as r
T=r.table(BASE/'k215.native.tm');T[198,0]=(0,-1,40)
def startup(start,limit=300000):
 q=start;h=0;ones=set()
 for tick in range(limit+1):
  if q==84 and ones and min(ones)==h-1:
   rights=[x for x in sorted(ones) if x>h-1]
   if rights and rights[0]>=h+64:
    header=rights[0];p=header+1;last=max(ones);v=[];good=True
    while p<=last:
     if p in ones or p+1 not in ones:good=False;break
     p+=1;n=0
     while p in ones:n+=1;p+=1
     v.append(n-1)
    if good and len(v)>=10 and v[0]==v[2]==v[7]==0:
     return dict(status='SEED',steps=tick,state=q,head=h,gap=header-h-64,registers=[v[j] for j in r.PHY],spares=v[9:],one_cells=sorted(ones))
  b=int(h in ones)
  if (q,b) not in T:return dict(status='HALT',steps=tick,state=q,head=h)
  w,d,z=T[q,b]
  if b==0 and z==q and(not ones or(d==1 and h>max(ones))or(d==-1 and h<min(ones))):return dict(status='RAY',steps=tick,state=q)
  if tick==limit:return dict(status='LIMIT',steps=tick,state=q)
  if w:ones.add(h)
  else:ones.discard(h)
  q=z;h+=d
results=[]
for start in sorted({q for q,b in T}):
 a=startup(start);results.append(dict(start=start,**a));print(start,{k:v for k,v in a.items() if k not in ('one_cells','spares')},flush=True)
Path('experiments/spares/all-starts-result.json').write_text(json.dumps(results,indent=2))
