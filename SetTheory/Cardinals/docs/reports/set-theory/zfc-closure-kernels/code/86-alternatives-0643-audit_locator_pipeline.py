#!/usr/bin/env python3
"""Independent literal-table/interface checks; universal proof in locator_pipeline_review.md."""
from pathlib import Path
import sys, json, hashlib, itertools, random
if not __debug__: raise SystemExit('Assertions must be enabled')
OUT=Path(__file__).resolve().parent; A=OUT.parent/'architectures';sys.path.insert(0,str(A))
import unary_locator as L
import integrated_oracle_locator as I

def parse(path):
 t={}
 for line in path.read_text().splitlines():
  if not line or line.startswith('#'):continue
  q,b,w,d,n=line.split(); q,b,w,n=map(int,(q,b,w,n))
  assert (q,b) not in t and b in (0,1) and w in (0,1) and d in ('L','R')
  t[q,b]=w,d,n
 return t

def run(t,q,halt,tape,h,cap=1000000,stop=None):
 tape=dict(tape)
 for steps in range(cap+1):
  if q==halt or q==stop:return tape,h,q,steps
  w,d,q=t[q,int(h in tape)]
  if w:tape[h]=1
  else:tape.pop(h,None)
  h+=1 if d=='R' else -1
 raise RuntimeError((q,h,cap))

def frame(i,records,gap=4,origin=0):
 # Independent positive-unary serialization; tuple values are lengths minus 1.
 tape={p:1 for p in range(origin-i,origin+1)}
 anchor=origin+gap+1;tape[anchor]=1;p=anchor+2;starts=[]
 for record in records:
  starts.append(p)
  for value in record:
   for k in range(value+1):tape[p+k]=1
   p+=value+2
 tape.pop(starts[0]);return tape,starts,p

loc=parse(A/'unary_locator_18.tm');pipeline=parse(A/'oracle_locator_pipeline_134.tm')
compiled,start,halt,o=I.compile_pipeline()
assert loc==L.compile_locator() and pipeline==compiled
assert set(loc)==set(itertools.product(range(18),range(2)))
assert set(pipeline)==set(itertools.product(range(134),range(2)))
counts={'locator_whole_tape_contexts':0,'pipeline_whole_tape_contexts':0}
maxsteps=0
values=list(itertools.product(range(3),repeat=3))
examples=[(a,) for a in values]+list(itertools.product(values,repeat=2))
rng=random.Random(20261018)
examples += [tuple(tuple(rng.randrange(20) for _ in range(3)) for _ in range(rng.randrange(1,16))) for _ in range(100)]
for records in examples:
 for i in range(len(records)):
  for gap,origin in ((2,-7),(4,0),(11,19)):
   tape,starts,end=frame(i,records,gap,origin)
   tape[origin-i-2]=1;tape[end+3]=1
   want=dict(tape);want[starts[0]]=1;want.pop(starts[i],None)
   for p in range(origin-i+1,origin+1):want.pop(p,None)
   actual,h,q,steps=run(loc,0,18,tape,origin)
   assert actual==want and h==starts[i]+1
   maxsteps=max(maxsteps,steps);counts['locator_whole_tape_contexts']+=1

# Independent tree enumeration/tag-output oracle, rather than using producer DFS.
def leaves(tree,path=(),bits=()):
 if tree[0] in ('z','p'):
  yield path,bits,0 if tree[0]=='z' else tree[1]+1
 else:
  for b in (0,1):yield from leaves(tree[1+b],path+(b,),bits+((tree[0]>>b)&1,))
records=[(0,0,0),(1,0,0),(2,0,1),(3,2,2),(0,1,3)]
collisions=[];example_collision=None
for rule,tree in o['syntax'].items():
 groups={}
 for path,bits,leaf in leaves(tree):
  output=bits+tuple(map(int,format(leaf,'03b')))
  groups.setdefault(output+(0,)*(28-len(output)),[]).append(list(path))
  for i in range(len(records)):
   for origin in (-17,0,23):
    offset=32+i
    tape,starts,end=frame(i,records,4,origin+offset)
    for j,b in enumerate(tuple(map(int,format(rule,'04b')))+path):
     if b:tape[origin+j]=1
    tape[origin-1]=1;tape[end+2]=1
    want=dict(tape)
    for j,b in enumerate(output):
     if b:want[origin+4+j]=1
     else:want.pop(origin+4+j,None)
    want[starts[0]]=1;want.pop(starts[i],None)
    for p in range(origin+33,origin+offset+1):want.pop(p,None)
    actual,h,q,steps=run(pipeline,start,halt,tape,origin)
    assert actual==want and h==starts[i]+1
    counts['pipeline_whole_tape_contexts']+=1
 for paths in groups.values():
  if len(paths)>1:collisions.append({'rule':rule,'paths':paths})
# Demonstrate the collision in the COMPLETE exit configurations, not just outputs.
configs=[]
for path in ([0,1,1,1],[1,0]):
 tape,starts,end=frame(2,records,4,34)
 for j,b in enumerate([0,0,1,1]+path):
  if b:tape[j]=1
 t,h,q,k=run(pipeline,start,halt,tape,0);configs.append((t,h,q))
assert configs[0]==configs[1]
# Independent blank probe sparse simulation and known exact 62-bit initializer.
blank=parse(A/'blank_pipeline_probe_197.tm')
assert set(blank)==set(itertools.product(range(197),range(2)))
t,h,q,k=run(blank,134,197,{},0)
assert k==198
firstpath=next(leaves(o['syntax'][3]))[0]
prepared,starts,end=frame(2,records[:3],4,34)
for j,b in enumerate((0,0,1,1)+firstpath):
 if b:prepared[j]=1
assert max(prepared)+1==62
pt,ph,pq,pk=run(pipeline,start,134,prepared,0)
assert t=={p-61:v for p,v in pt.items()} and h==ph-61 and k==63+pk
# Reachable malformed inputs explicitly do not have reject-and-restart semantics.
malformed=[]
t,h,q,k=run(pipeline,start,134,{},0,cap=100,stop=119)
assert q==119;malformed.append({'case':'rule 0 on blank tape','sink_state':q,'steps_to_sink':k})
bad,_,_=frame(1,[(0,0,0)],4)
t,h,q,k=run(loc,0,18,bad,0,stop=17)
assert q==17;malformed.append({'case':'index equal to arena length','sink_state':q,'steps_to_sink':k})
# All-zero locator input follows q0/0 left forever, without reaching even reject.
assert loc[0,0]==(0,'L',0)
result={'status':'PASS_VALID_FRAME_COMPONENTS','counts':counts,'maximum_locator_steps':maxsteps,
 'state_counts':{'locator':18,'pipeline':134,'blank_probe':197},
 'blank_probe':{'steps':198,'head':ph-61},
 'query_information_loss':{'collision_groups':len(collisions),'example':{'rule':3,'paths':[[0,1,1,1],[1,0]],'complete_exit_configurations_identical':True}},
 'malformed_examples':malformed,'all_zero_locator':'q0 moves left forever',
 'hashes':{p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in [A/'unary_locator.py',A/'unary_locator_18.tm',A/'integrated_oracle_locator.py',A/'oracle_locator_pipeline_134.tm',A/'blank_pipeline_probe_197.tm',A/'pattern_oracle.py']}}
(OUT/'locator_pipeline_independent_audit.json').write_text(json.dumps(result,indent=2)+'\n')
(OUT/'pipeline_path_collisions.json').write_text(json.dumps(collisions,indent=2)+'\n')
print(json.dumps(result,indent=2))
