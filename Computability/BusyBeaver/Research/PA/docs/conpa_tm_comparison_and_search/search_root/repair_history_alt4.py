"""Search existing excursions for the two relocated 2037 interfaces."""
import sys,json,itertools,time
from pathlib import Path
from collections import defaultdict
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'research_ipra/newsearch'))
import rotation_search as a
BASE=Path('support/alternative196')
original={}
for ln in (BASE/'alternative196.native.tm').read_text().splitlines():
 if not ln.strip() or ln.startswith('#'):continue
 q,b,w,d,n=ln.split();original[int(q),int(b)]=(int(w),d=='R',int(n))
j=json.loads(Path('research208/alt_only_router195.json').read_text())
rows={(q,b):(w,d,n) for q,b,w,d,n in j['rows']}
sites=[(tuple(p),op,arg) for p,op,arg in j['sites']]
tr={}
for p,op,arg in sites:
 x=tr
 for bit in p[:-1]:x=x.setdefault(bit,{})
 x[p[-1]]=('leaf',op,arg)
def convert(x):return (convert(x[0]),convert(x[1])) if isinstance(x,dict) else x
t=convert(tr)
sites,contracts=a.contract_list(t)
oldnodes=a.ns
shapes={a.expand('x55'):0,a.expand('x23'):1}
goals={}
for prev in (0,1):
 for bit in (0,1):
  h=original[2037,bit][2];u=original[h,prev][2]
  goals[prev,bit]=original[u,bit]
print('goals',goals,flush=True)

def leftbits(left):
 out=[]
 for x in left:
  if x[0]=='b':out.append(x[1])
  elif x[0]=='r' and x[2]==0:out.extend([x[1]]*x[3])
  else:return None
 while out and out[-1]==0:out.pop()
 return tuple(reversed(out))[1:]

def desired(s):
 q,onl,left,right=s
 if q!=2037 or onl:return None
 b=a.headbit(right);path=leftbits(left)
 if path is None:return None
 tt=t
 for x in path:
  if a.leaf(tt):raise ValueError(('leafprefix',path))
  tt=tt[x]
 if tt not in shapes:raise ValueError(('unknownshape',path))
 return goals[shapes[tt],b]

contexts=defaultdict(dict)
def ideal_run(contract):
 site,br,s,target=contract;moved=False
 for k in range(1024):
  if moved and (s[0]==254 if target is None else a.matches(s,target)):return k
  wanted=desired(s)
  if wanted:
   b=a.headbit(s[3]);contexts[b][s]=wanted
   temp=dict(rows);temp[2037,b]=wanted
  else:temp=rows
  n=a.sstep(temp,br,s)
  if n is None:return None
  s,m=n;moved|=m
 return None

start=time.time();fail=[]
for c in contracts:
 n=ideal_run(c)
 if n is None:fail.append(c[0])
print('ideal failures',fail[:40],'counts',len(fail),{k:len(v) for k,v in contexts.items()},'sec',time.time()-start,flush=True)
if fail:print("NOTE: additional non-router failure retained",flush=True)

RAD=45;LIMIT=180
def take(segs,n):
 out=[]
 for x in segs:
  if x[0]=='b':out.append(x[1])
  elif x[0]=='r':
   out.extend([x[1]]*min(n-len(out),x[3]))
   if x[2] and len(out)<n:break
  else:out.append(0);break
  if len(out)>=n:break
 return tuple(out[:n])+(-1,)*max(0,n-len(out))
def reaches(act,tape,goal):
 w,d,n=goal;target=RAD+(1 if d else -1);expected=tape[:RAD]+(w,)+tape[RAD+1:]
 ww,dd,q=act;tp=list(tape);tp[RAD]=ww;h=RAD+(1 if dd else -1)
 for step in range(LIMIT):
  if q==n and h==target and tuple(tp)==expected:return True
  if h<0 or h>=len(tp) or tp[h]<0:return False
  if q==2037:return False
  z=rows.get((q,tp[h]))
  if z is None:return False
  ww,dd,q=z;tp[h]=ww;h+=1 if dd else -1
 return False
states=sorted({q for q,b in rows}); qi={q:i for i,q in enumerate(states)}
dataset=[]
for bit,cx in contexts.items():
 for s,goal in cx.items():
  tape=tuple(reversed(take(s[2],RAD)))+take(s[3],RAD+1)
  dataset.append((bit,goal[2],tape))
dataset=list(dict.fromkeys(dataset))
# Put altered C interfaces and a close old H interface early.
dataset.sort(key=lambda z:(0 if z[1]==90 and z[2][RAD-1]==1 else 1, z[0], -z[2].count(-1)))
filename=Path(__file__).with_suffix('.contexts.txt')
with filename.open('w') as f:
 f.write(f'{len(states)} {qi[2037]} {RAD} {LIMIT} {len(dataset)}\n')
 f.write(' '.join(map(str,states))+'\n')
 for q in states:
  f.write(' '.join(str(v) for bit in (0,1) for v in (rows[q,bit][0],1 if rows[q,bit][1] else -1,qi.get(rows[q,bit][2],-1)))+'\n')
 for bit,target,tp in dataset:
  f.write(f'{bit} {qi[target]} '+' '.join(map(str,tp))+'\n')
options={}
for bit,cx in contexts.items():
 actions={(w,d,q) for q,b in rows if b==0 and q!=2037 for w in (0,1) for d in (False,True)}
 pairs={(tuple(reversed(take(s[2],RAD)))+take(s[3],RAD+1),goal) for s,goal in cx.items()}
 pairs=sorted(pairs,key=lambda z:z[0].count(-1),reverse=True)
 for i,(tp,g) in enumerate(pairs):
  actions={v for v in actions if reaches(v,tp,g)}
  if not actions:break
 options[bit]=sorted(actions)
 print('options',bit,len(pairs),'checked',i+1,options[bit],flush=True)
Path(__file__).with_suffix('.result.json').write_text(json.dumps({'ideal_failures':fail,'context_counts':{k:len(v) for k,v in contexts.items()},'options':options,'radius':RAD,'step_limit':LIMIT},indent=2))
for zero,one in itertools.product(options.get(0,[]),options.get(1,[])):
 rr=dict(rows);rr[2037,0]=zero;rr[2037,1]=one
 result=a.validate(rr,contracts);print('RESULT',zero,one,result,flush=True)
 if result['ok']:
  Path('search_root/alt_only_router_candidate195.json').write_text(json.dumps({'rows':[[q,b,*v] for(q,b),v in sorted(rr.items())],'sites':sites,'validation':result},indent=2));break
