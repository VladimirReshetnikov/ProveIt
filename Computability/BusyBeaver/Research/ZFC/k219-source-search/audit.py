#!/usr/bin/env python3
"""Own finite checks supporting proof.md; no binary runtime certification."""
from model import *
import argparse,random,time
ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--output',type=Path,required=True)
a=ap.parse_args();assert __debug__;assert not a.output.exists()
started=time.monotonic();tree,rows=load();g=graph(rows);ns=nodes(tree)
rotations=[];counts=collections.Counter();ntry=0
for i,t in enumerate(ns):
 if leaf(t):continue
 l,r=t;opts=[]
 if not leaf(l):opts.append(('right',(l[0],(l[1],r)),boundary(l[0])[0]==0 and boundary(r)[1]==0))
 if not leaf(r):opts.append(('left',((l,r[0]),r[1]),boundary(l)[0]==0 and boundary(r[1])[1]==0))
 for direction,new,rule in opts:
  ntry+=1;z=replace(tree,t,new);zr=leaves(z);same=graph(zr)==g
  assert same==rule,(i,direction)
  if same:
   m=metrics(z);counts[m['dag_nodes']]+=1;rotations.append(dict(node=i,direction=direction,metrics=m))
assert ntry==295 and len(rotations)==210 and min(counts)==206
# Own abstract transfer, bucket8 is unbounded above, not a numerical cutoff.
limit=8;full=(1<<(limit+1))-1;states=[None]*len(g)
seed=[3,0,0,0,3,0,0,0,0];states[0]=tuple(1<<x for x in seed)
def transfer(i,s):
 o,r,ts=g[i]
 if o=='CH':return []
 if o in ('CB','CC'):return [(ts[0],s)]
 if o=='CI':
  v=list(s);v[r]=((s[r]<<1)&full)|(s[r]&(1<<limit));return [(ts[0],tuple(v))]
 out=[]
 if s[r]&1:
  v=list(s);v[r]=1;out.append((ts[0],tuple(v)))
 if s[r]&~1:
  v=list(s);v[r]=(s[r]>>1)|(s[r]&(1<<limit));out.append((ts[1],tuple(v)))
 return out
todo=collections.deque([0]);pending={0};updates=0
while todo:
 i=todo.popleft();pending.remove(i)
 for j,v in transfer(i,states[i]):
  new=v if states[j] is None else tuple(x|y for x,y in zip(v,states[j]))
  if new!=states[j]:
   states[j]=new;updates+=1
   if j not in pending:todo.append(j);pending.add(j)
edges=0
for i,s in enumerate(states):
 if s is None:continue
 for j,v in transfer(i,s):
  edges+=1;assert states[j] is not None and all(x&~y==0 for x,y in zip(v,states[j]))
assert all(states[0][i]>>r&1 for i,r in enumerate(seed))
dead=[i for i,s in enumerate(states) if s is None]
forced=[i for i,(o,r,_) in enumerate(g) if o=='CD' and states[i] is not None and states[i][r]==1]
assert dead==[4607,4719,4720] and forced==[4606,4718] and states[4598][6]==1
# Inventory all delivered hits and regenerate the five proved alternatives.
accepted=freeze(json.loads((BASE/'new_equality_macro.json').read_text()))
hits=json.loads(HITS.read_text());inventory=[];rng=random.Random(219207)
cases=[(x,y) for x in range(13) for y in range(13)]
cases += [(0,10000),(10000,0),(10000,10000),(9999,10000),(10000,9999)]
cases += [(rng.randrange(1001),rng.randrange(1001)) for _ in range(20)]
def run(t,x,y):
 gg=localg(t);regs=[17,19,23,29,31,x,y,37,41];pc=0
 for tick in range(64*(x+y+2)):
  o,r,ts=gg[pc]
  if o=='CI':regs[r]+=1;pc=ts[0]
  elif o=='CD':
   pos=regs[r]>0
   if pos:regs[r]-=1
   pc=ts[int(pos)]
  elif o in ('CB','CC'):pc=ts[0]
  else:raise AssertionError('Unexpected halt')
  if pc<0:return pc,regs,tick+1
 raise AssertionError(('finite diagnostic budget',x,y))
finite=[]
for i,h in enumerate(hits):
 h=freeze(h);z=replace(tree,accepted,h);rr=leaves(h);m=metrics(z)
 right=[list(r) for r in rr if r[1]=='CD' and r[0][-1]=='1']
 inventory.append(dict(hit=i,metrics=m,macro_leaves=len(rr),macro_nodes=len(nodes(h)),right_decrements=right))
 if i not in (0,1,2,3,12):continue
 out=HERE/'candidates'/f'hit{i:02d}.sites.json';raw=(json.dumps(leaves(z),separators=(',',':'))+'\n').encode()
 assert out.read_bytes()==raw and graph(leaves(z))==arithmetic_graph(leaves(z))
 maximum=0;steps=0
 for x,y in cases:
  status,regs,k=run(h,x,y);want=[17,19,23,29,31,0,0,37,41]
  assert status==(-1 if x==y else -2) and regs==want,(i,x,y,status,regs)
  maximum=max(maximum,k);steps+=k
 finite.append(dict(hit=i,cases=len(cases),primitive_steps=steps,max_steps=maximum,source_sha256=hashlib.sha256(raw).hexdigest()))
# Important negative controls for unrestricted association.
x=('CB',1);y=('CI',0);z=('CI',1)
assert localg(((x,y),z))!=localg((x,(y,z)))
x=('CI',0);y=('CI',1);z=(('CD',0),('CC',2))
assert localg(((x,y),z))!=localg((x,(y,z)))
aff=[affine(t) for t in ns if affine(t) is not None]
assert len(aff)==35 and len(set(aff))==35
result=dict(status='SOURCE_ANALYSIS_AND_FINITE_DIAGNOSTICS_PASS',scope='Ordinary proof.md supplies all-natural arguments; this run is a finite syntax/CFG/abstract-closure/diagnostic audit, no binary table or proof-assistant check.',
 input_sha256=hashlib.sha256((BASE/'sites219.json').read_bytes()).hexdigest(),equality_hits_sha256=hashlib.sha256(HITS.read_bytes()).hexdigest(),script_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
 rotations_attempted=ntry,exact_rotations=len(rotations),rotation_costs=dict(counts),rotations=rotations,
 seed_abstraction=dict(seed=seed,bucket_limit=limit,updates=updates,closure_edges=edges,dead_ordinals=dead,forced_zero_ordinals=forced),
 affine_blocks=len(aff),distinct_affine_transformers=len(set(aff)),equality_inventory=inventory,equality_diagnostics=finite,negative_controls=2,seconds=time.monotonic()-started)
a.output.parent.mkdir(parents=True,exist_ok=True);a.output.write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:v for k,v in result.items() if k not in ('rotations','equality_inventory')},indent=2))
