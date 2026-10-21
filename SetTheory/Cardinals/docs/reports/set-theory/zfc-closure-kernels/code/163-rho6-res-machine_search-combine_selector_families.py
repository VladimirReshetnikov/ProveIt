import json,itertools,sys
from pathlib import Path
from collections import defaultdict
P=Path(__file__).parent
prefix=sys.argv[1] if len(sys.argv)>1 else '';lines=(P/(prefix+'allbranch-options.txt')).read_text().splitlines();B=defaultdict(lambda:[[],[]])
# Use None for unconstrained helper row domain.
for line in lines:
 a=line.split();tag=a.pop(0);xs=list(map(int,a));keep,drop,bit=xs[:3];xs=xs[3:]
 if tag=='DIRECT':
  count=xs.pop(0);assert len(xs)==3*count
  B[keep,drop][bit].append((tuple(tuple(xs[3*i:3*i+3])for i in range(count)),None,None))
 else:
  fw,fd=xs[:2];xs=xs[2:];n0=xs.pop(0);h0=frozenset(tuple(xs[3*i:3*i+3])for i in range(n0));xs=xs[3*n0:];n1=xs.pop(0);h1=frozenset(tuple(xs[3*i:3*i+3])for i in range(n1));xs=xs[3*n1:];assert not xs
  B[keep,drop][bit].append((((fw,fd,500),),h0,h1))
def inter(a,b):return b if a is None else a if b is None else a&b
variants=[]
for (keep,drop),opts in B.items():
 for l,r in itertools.product(*opts):
  h0=inter(l[1],r[1]);h1=inter(l[2],r[2])
  if h0==frozenset()or h1==frozenset():continue
  assert h0 is not None and h1 is not None
  variants.append({'k':keep,'d':drop,'a0':l[0],'a1':r[0],'h0':h0,'h1':h1})
print('branch families',sum(len(v[0])+len(v[1])for v in B.values()),'complete fold variants',len(variants))
print('foldpairs',sorted({(v['k'],v['d'])for v in variants}))
C=[]
for i,v in enumerate(variants):
 for u in variants[i+1:]:
  if (v['k'],v['d'])==(u['k'],u['d']):continue
  nodes={v['k'],v['d'],u['k'],u['d']};parents={x:x for x in nodes}
  def phi(x):
   while x in parents and parents[x]!=x:x=parents[x]
   return x
  for vv in (v,u):
   a,b=phi(vv['k']),phi(vv['d']);parents[max(a,b)]=min(a,b)
  maps={x:phi(x)for x in nodes if phi(x)!=x};assert len(maps)==2
  def act(x):return x[:2]+(phi(x[2]),)
  h0={act(x)for x in v['h0']}&{act(x)for x in u['h0']};h1={act(x)for x in v['h1']}&{act(x)for x in u['h1']}
  if not h0 or not h1:continue
  groups=defaultdict(lambda:[None,None]);good=True
  for vv in(v,u):
   k=phi(vv['k'])
   for bit in(0,1):
    aa={act(x)for x in vv['a'+str(bit)]};groups[k][bit]=inter(groups[k][bit],aa)
    if not groups[k][bit]:good=False
  if not good:continue
  slots=[];choices=[]
  for q,rr in groups.items():
   for bit in(0,1):slots.append((q,bit));choices.append(sorted(rr[bit]))
  slots.extend([(500,0),(500,1)]);choices.extend([sorted(h0),sorted(h1)])
  for cc in itertools.product(*choices):C.append({'maps':maps,'rows':[(q,bit,*row)for(q,bit),row in zip(slots,cc)],'variants':[i,variants.index(u)]})
print('combined candidates',len(C))
# JSON serialization for research provenance.
(P/(prefix+'allbranch-variants.json')).write_text(json.dumps([{k:list(value)if isinstance(value,frozenset)else value for k,value in v.items()}for v in variants],indent=2))
(P/(prefix+'combined-candidates.json')).write_text(json.dumps(C,indent=2))
with (P/(prefix+'combined-candidates.txt')).open('w')as f:
 for c in C:
  f.write('CAND '+str(len(c['maps']))+' '+ ' '.join(f'{a} {b}'for a,b in c['maps'].items())+' '+str(len(c['rows']))+' '+' '.join(' '.join(map(str,r))for r in c['rows'])+'\n')
