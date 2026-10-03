import json,time
from test_compiler import fusion,expected_path,flip
start=time.time(); results=[]
for side,c in [(-1,0),(-1,2),(1,0),(1,2)]:
 C=fusion(side);cs=[0,0];cs[0 if side==-1 else 1]=c
 path=expected_path(C,'START',*cs); T=len(path)-1
 cycle=path+[flip(C,x) for x in reversed(path)]
 assert len(cycle)==2*T+2 and len(set(cycle))==len(cycle)
 x=cycle[0]; hits=[]
 haltword={0,C.S,C.S+C.gap[(('H','HALT'),'+')]}
 for t,want in enumerate(cycle):
  assert x==want,(side,c,t)
  if {u for u in x if 0<=u<=C.S+C.D}==haltword:hits.append(t)
  x=C.step(x)
 assert x==cycle[0]
 assert hits==[T],(side,c,hits,T)
 results.append(dict(side=side,input_counter=c,forward_halt_time=T,cycle_length=len(cycle),observer_hits=hits))
 print('cycle passed',results[-1],flush=True)
receipt=dict(status='passed',cycles=results,seconds=time.time()-start)
open('full-cycle-receipt.json','w').write(json.dumps(receipt,indent=2)+'\n')
