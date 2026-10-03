import json,random,time
from reversible_binary import compile_source
# Loading helper test module also reruns its independent regression set.
from test_compiler import expected_path,flip
start=time.time(); receipt=[]
for side in (-1,1):
 idx=0 if side==-1 else 1
 C=compile_source(dict(schema='reversible-two-counter-v1',controls=['START','HALT'],
  start='START',halt='HALT',class_cut=1,branches=[dict(name='dec',source='START',
  target='HALT',side=side,delta=-1,guard=dict(op='gt',counter=idx,value=0))]))
 for value in (0,1,3):
  cs=[0,0];cs[idx]=value;path=expected_path(C,'START',*cs)
  cycle=path+[flip(C,x) for x in reversed(path)]; x=cycle[0]
  hits=[]; word={0,C.S,C.S+C.gap[(('H','HALT'),'+')]}
  for t,want in enumerate(cycle):
   assert x==want,(side,value,t)
   if {z for z in x if 0<=z<=C.S+C.D}==word:hits.append(t)
   x=C.step(x)
  assert x==cycle[0]
  assert hits==([len(path)-1] if value>0 else [])
  receipt.append(dict(side=side,counter=value,cycle=len(cycle),halt_hits=hits))
# Deliberately malformed neighborhoods with multiple heads and altered guard bits.
rng=random.Random(42); trials=0
base=C.encode('START',3,2)
for noise in range(50):
 x=set(base)
 for k in range(rng.randrange(1,8)):
  z=rng.randrange(-2*C.Z,2*C.Z)
  if z in x:x.remove(z)
  else:x.add(z)
 if noise%2:x.update(z+2*C.B3 for z in base)
 x=frozenset(x);y=C.step(x,verify=True)
 assert len(x)==len(y) and C.step(y,inverse=True,verify=True)==x
 trials+=1
out=dict(status='passed',decrement_cycles=receipt,malformed_noise=trials,seconds=time.time()-start)
open('additional-receipt.json','w').write(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
