import sys,json,time,itertools
from fractions import Fraction
from math import gcd,lcm
from pathlib import Path
ROOT=Path('/home/codex/.codex/worktrees/9348/Proofs/Topology/UnknotRecognition');sys.path.insert(0,str(ROOT/'fast'))
from fastunknot.normal_surface_geometry import _prepare
from fastunknot.normal_sector import _discover_in_kernel
from fastunknot.sector_sparse import PreparedSectorSource
from fastunknot import Diagram
from fastunknot.normal_seed_verify import verify_normal_seed_certificate
from fastunknot.integer_codec import json_safe
def add(v,w,scale=1):
 v=v.copy()
 for i,z in w.items():
  v[i]=v.get(i,0)+scale*z
  if not v[i]:del v[i]
 return v
def primitive(v):
 if not v:return (),0
 den=lcm(*(z.denominator for z in v.values()));ints={i:int(z*den)for i,z in v.items()};g=gcd(*ints.values());sgn=1 if ints[min(ints)]>0 else -1
 return tuple((i,z//(g*sgn))for i,z in sorted(ints.items())),sgn
def matrix(p):
 n=len(p['tetrahedra']);adj=[[]for _ in range(4*n)];edges=[];rows=[]
 for eq in p['matching']:
  ts={4*(i//7)+i%7:z for i,z in eq.items()if i%7<4};q={3*(i//7)+i%7-4:z for i,z in eq.items()if i%7>=4}
  if not ts:rows.append(q);continue
  a=next(i for i,z in ts.items()if z==1);b=next(i for i,z in ts.items()if z==-1);edges.append((a,b,q));adj[a].append((b,q));adj[b].append((a,{i:-z for i,z in q.items()}))
 pot=[None]*(4*n)
 for root in range(4*n):
  if pot[root]is not None:continue
  pot[root]={};queue=[root]
  for a in queue:
   for b,q in adj[a]:
    if pot[b]is None:pot[b]=add(pot[a],q);queue.append(b)
 for a,b,q in edges:rows.append(add(add(pot[b],pot[a],-1),q,-1))
 rows=sorted({primitive(r)[0]for r in rows if r});cols=[{}for _ in range(3*n)]
 for j,row in enumerate(rows):
  for i,z in row:cols[i][j]=z
 return cols
def reduce(v,basis):
 for i,w in sorted(basis.items()):
  if i in v:v=add(v,w,-v[i])
 return v
def plan(raw,base):
 cols=matrix(_prepare(raw,lambda:None));basis={}
 for t,q in enumerate(base):
  if q<0:continue
  v=reduce(cols[3*t+q],basis)
  if v:
   i=min(v);scale=Fraction(v[i]);basis[i]={j:z/scale for j,z in v.items()}
 zero=[];groups={}
 for t,q in itertools.product(range(len(base)),range(3)):
  if q==base[t]:continue
  key,sign=primitive(reduce(cols[3*t+q],basis))
  if not key:zero.append((t,q))
  else:groups.setdefault(key,{1:[],-1:[]})[sign].append((t,q))
 singles=[(x,)for x in zero];pairs=[(a,b)for a,b in itertools.combinations(zero,2)if a[0]!=b[0]]
 for group in groups.values():pairs += [tuple(sorted((a,b)))for a,b in itertools.product(group[1],group[-1])if a[0]!=b[0]]
 return singles,sorted(set(pairs)),len(groups)
x=json.load(open('/tmp/unknot-radius-two.json'));raw=x['triangulation'];base=x['base_signature'];start=time.perf_counter();singles,pairs,groups=plan(raw,base);print('PLAN',len(singles),len(pairs),groups,'seconds',time.perf_counter()-start,flush=True)
print('target index',pairs.index(((10,1),(12,2))),flush=True)
shared=PreparedSectorSource(raw);found=None;queries=0
for edits in singles+list(pairs):
 sig=list(base)
 for t,q in edits:sig[t]=q
 k=shared.build([(t,q)for t,q in enumerate(sig)if q>=0]);a=_discover_in_kernel(k,phase='standard');queries+=1
 if a['status']=='DISC_FOUND':
  c=a['certificate'];found=dict(schema='diagram-normal-disc-v1',input_pd=x['source']['pd'],triangulation=raw,coordinates=c['coordinates'],disc_certificate=c['disk_certificate']);assert verify_normal_seed_certificate(Diagram.from_pd(x['source']['pd']),found);print('DISC',edits,queries,'seconds',time.perf_counter()-start,flush=True);break
open('/tmp/unknot-residual-probe.json','w').write(json.dumps(json_safe(dict(singles=singles,pairs=pairs,groups=groups,queries=queries,seconds=time.perf_counter()-start,proof=found)),indent=2)+'\n')
