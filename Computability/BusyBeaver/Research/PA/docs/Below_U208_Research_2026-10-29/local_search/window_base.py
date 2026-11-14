from pathlib import Path
from collections import defaultdict,deque
import json,itertools,time
P=Path(__file__).resolve().parent
base=P/'inputs/contextual211.tm'
def read(p):
 T={}
 for l in p.read_text().splitlines():
  if not l or l.startswith('#'):continue
  q,b,w,d,z=l.split();T[int(q),int(b)]=(int(w),1 if d=='R'else-1,int(z))
 return T
def write(T,p):
 p.write_text('#! start 0\n'+''.join(f'{q} {b} {w} {"R"if d==1 else"L"} {z}\n'for(q,b),(w,d,z)in sorted(T.items())))
def abstract(T,r=3):
 n=2*r+1;mask=(1<<n)-1;seen={(0,0)};todo=deque(seen);Q={q for q,b in T}
 while todo:
  q,v=todo.popleft();b=(v>>r)&1;w,d,z=T[q,b]
  if z not in Q:continue
  v=(v&~(1<<r))|(w<<r)
  vs=[(v>>1)|(a<<(n-1))for a in(0,1)]if d==1 else[((v<<1)&mask)|a for a in(0,1)]
  for v in vs:
   if (z,v)not in seen:seen.add((z,v));todo.append((z,v))
 out=defaultdict(list)
 for q,v in seen:out[q].append(v)
 return out
def endpoints(T,q,cells,limit=16):
 h=0;t=cells.copy();out=[]
 for k in range(limit):
  if h not in t or(q,t[h])not in T:break
  w,d,q=T[q,t[h]];t[h]=w;h+=d;out.append((q,h,tuple(sorted(t.items()))))
 return out

def search(T,label):
 I=abstract(T);Q=sorted({q for q,b in T});pairs=0;tests=0
 for a,c in itertools.combinations(Q,2):
  shared=[b for b in(0,1)if T[a,b]==T[c,b]]
  if len(shared)!=1 or 0 in(a,c):continue
  b=1-shared[0]
  # retain c, remove a; each original abstract local window must join in <=16steps
  rho=lambda x:c if x==a else x
  C={(q,x):(w,d,rho(z))for(q,x),(w,d,z)in T.items()if q!=a}
  contexts=[]
  for q in(a,c):
   for v in I[q]:
    if ((v>>3)&1)!=b:continue
    cells={i-3:(v>>i)&1 for i in range(7)}
    old=endpoints(T,q,cells)
    old=[(rho(z),h,t)for z,h,t in old if z!=a] # joins cannot be deletedstate
    contexts.append((cells,set(old)))
  if not contexts:continue
  pairs+=1
  for w,d,z in itertools.product((0,1),(-1,1),Q):
   if z==a:continue
   C[c,b]=(w,d,z);tests+=1
   if all(any(e in ends for e in endpoints(C,c,cell))for cell,ends in contexts):
    out=P/f'{label}_fold_{a}_{c}_{b}_{w}_{d}_{z}.tm';write(C,out)
    print('FOUND',out.name,flush=True)
    return C
 print(label,'no fold',pairs,tests,'windows',sum(map(len,I.values())),flush=True)
 return None
