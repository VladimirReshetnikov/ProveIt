#!/usr/bin/env python3
"""Independent literal counterexample replay; no received programs imported."""
import hashlib,json
from pathlib import Path
D=Path(__file__).resolve().parent;ROOT=D.parent
path=ROOT/'latest219_baseline/candidate-k219/k219.native.tm';T={}
for line in path.read_text().splitlines():
 if line and not line.startswith('#'):
  q,b,w,d,n=line.split();T[int(q),int(b)]=int(w),1 if d=='R' else -1,int(n)
PHY=[6,2,0,4,3,7,8,5,1]
def frame(pc,regs,spares,gap):
 phy=[0]*9
 for i,j in enumerate(PHY):phy[j]=regs[i]
 ones={-1,64+gap}|{i for i,b in enumerate(pc) if b=='1'};pos=65+gap
 for n in phy+spares:
  assert n>=0
  pos+=1;ones.update(range(pos,pos+n+1));pos+=n+1
 return ones

def inspect_clean(q,h,ones):
 if q!=84 or h-1 not in ones or any(x<h-1 for x in ones):return None
 candidates=[x for x in ones if x>=h+52]
 if not candidates:return None
 header=min(candidates)
 if header<h+64:return None
 pos=header+1;last=max(ones);values=[]
 while pos<=last:
  if pos in ones or pos+1 not in ones:return None
  start=pos+1;pos=start
  while pos in ones:pos+=1
  values.append(pos-start-1)
 if pos!=last+1 or len(values)<10:return None
 regs=[values[j] for j in PHY]
 codeones=sorted(x-h for x in ones if h<=x<header)
 pc=''.join('1' if i in codeones else '0' for i in range(max(codeones)+1)) if codeones else ''
 return {'minimal_pc':pc,'registers':regs,'spares':values[9:],'gap':header-h-64}

def run(tm,initial,cap=2000):
 q=84;h=0;ones=set(initial);trace=[];dispatches=[]
 for tick in range(cap+1):
  if tick and q==84:
   clean=inspect_clean(q,h,ones);dispatches.append({'tick':tick,'head':h,'clean':clean})
   if clean is not None:return {'steps':tick,'state':q,'head':h,'ones':sorted(ones),'decoded':clean,'trace':trace,'dispatcher_visits':dispatches}
  assert tick<cap
  read=int(h in ones);write,delta,nxt=tm[q,read]
  trace.append([tick,q,h,read,write,delta,nxt])
  if write:ones.add(h)
  else:ones.discard(h)
  h+=delta;q=nxt

regs=[0]*8+[1];initial=frame('000',regs,[0],0)
expected=frame('001',[0]*9,[0],1)
base=run(T,initial)
assert base['steps']==600 and base['state']==84 and base['head']==0 and set(base['ones'])==expected
reports=[]
received=json.loads((ROOT/'research218_encoding/COOPERATIVE27_CONCRETE_DIAGNOSIS.json').read_text())['results']
for rec in received:
 U={row:act for row,act in T.items() if row[0]!=302}
 U[103,1]=(0,-1,162);U[113,0]=(0,-1,27);U[27,0]=tuple(rec['action'])
 ans=run(U,initial)
 assert ans['steps']==rec['steps']
 assert ans['trace']==rec['trace']
 assert ans['ones']==rec['actual']['ones'] and ans['head']==rec['actual']['head'] and rec['actual']['state']==96
 assert initial==set(rec['initial_one_cells']) and expected==set(rec['expected']['ones'])
 assert ans['decoded']=={'minimal_pc':'01','registers':regs,'spares':[0],'gap':0}
 assert set(ans['ones'])!=expected
 reports.append({'action':rec['action'],'status':'INDEPENDENT_CONCRETE_INTERFACE_REFUTATION','steps':ans['steps'],'first_clean_dispatch':ans['decoded'],'native_state':ans['state'],'head':ans['head'],'whole_tape_ones':ans['ones'],'full_literal_trace_matches_received':True,'all_earlier_dispatch_visits_nonclean':all(r['clean'] is None for r in ans['dispatcher_visits'][:-1])})
result={'status':'FOUR_INDEPENDENT_COUNTEREXAMPLE_REPLAYS_PASS','baseline_native_sha256':hashlib.sha256(path.read_bytes()).hexdigest(),'initial':{'source_leaf':'000/CD8','registers':regs,'gap':0,'spares':[0],'one_cells':sorted(initial)},'required':{'source_pc':'001','registers':[0]*9,'gap':1,'spares':[0],'one_cells':sorted(expected)},'baseline_steps':600,'counterexamples':reports,'scope':'Concrete valid generic primitive-interface counterexamples only; no claim these frames occur on the initialized blank run. Does not refute all possible302 deletions or other helper repairs.'}
(D/'COOPERATIVE27_COUNTEREXAMPLE_AUDIT.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
