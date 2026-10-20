from pathlib import Path
from collections import deque,defaultdict
import json,sys,time,itertools

def read_table(path):
 t={}
 for l in Path(path).read_text().splitlines():
  if l and l[0]!='#':
   q,b,w,d,z=l.split();t[int(q),int(b)]=(int(w),1 if d=='R' else -1,int(z))
 return t

def invariants(t,radius=6,start=0):
 states={q for q,b in t};f={q:None for q in states};f[start]={};work=deque([start]);todo={start}
 while work:
  q=work.popleft();todo.remove(q)
  for b in (0,1):
   a=dict(f[q])
   if 0 in a and a[0]!=b:continue
   a[0]=b;w,d,z=t[q,b]
   if z not in states:continue
   a[0]=w;new={k-d:v for k,v in a.items() if -radius<=k-d<=radius}
   old=f[z]
   if old is not None:new={k:v for k,v in old.items() if new.get(k)==v}
   if old!=new:
    f[z]=new
    if z not in todo:todo.add(z);work.append(z)
 return {q:a or {} for q,a in f.items()}

def block(t,entry,initial,target,first=None,limit=18,banned=()):
 q=entry;h=0;tp=dict(initial);z,eh,et=target
 for tick in range(limit):
  if h not in tp or (q,tp[h]) not in t:return False
  if tick and q in banned:return False
  w,d,q=(first if tick==0 and first is not None else t[q,tp[h]])
  tp[h]=w;h+=d
  if q==z and h==eh and tp==et:return True
 return False

def encode(t):
 return '#! start 0\n'+''.join(f'{q} {b} {w} {"R" if d==1 else "L"} {z}\n' for (q,b),(w,d,z) in sorted(t.items()))

def search(t,out):
 started=time.time();states=sorted({q for q,b in t});facts=invariants(t);permitted={};actions=[(w,d,z) for w in (0,1) for d in (-1,1) for z in states if z!=0]
 for i,q in enumerate(states):
  if q==0:continue
  for b in (0,1):
   if facts[q].get(0,b)!=b:permitted[q,b]=None;continue
   initial=facts[q]|{0:b};w,d,z=t[q,b];expected=initial|{0:w}
   matches=[]
   for act in actions:
    if block(t,q,initial,(z,d,expected),act,banned=(q,)):matches.append(act)
   permitted[q,b]=set(matches)
  if i%25==0:print('actions',i,'elapsed',time.time()-started,flush=True)
 found=[]
 for p,q in itertools.combinations([q for q in states if q!=0],2):
  # Simple endpoint-preserving folds need no involved-state recurrence.
  ps=[]
  for b in (0,1):
   a,c=permitted[p,b],permitted[q,b]
   v=(a&c if a is not None and c is not None else a if a is not None else c)
   if v is None:v={t[p,b]}
   if not v:break
   ps.append(v)
  if len(ps)!=2:continue
  for a0,a1 in itertools.product(*ps):
   phi=lambda s:p if s==q else s
   new={(s,b):(w,d,phi(z)) for (s,b),(w,d,z) in t.items() if s!=q}
   new[p,0]=(a0[0],a0[1],phi(a0[2]));new[p,1]=(a1[0],a1[1],phi(a1[2]))
   good=True
   for s,b in itertools.product((p,q),(0,1)):
    if facts[s].get(0,b)!=b:continue
    initial=facts[s]|{0:b};w,d,z=t[s,b];expected=initial|{0:w}
    if not block(new,p,initial,(phi(z),d,expected)):good=False;break
   if good:
    spec={'keep':p,'delete':q,'a0':a0,'a1':a1,'invariant':{s:fs for s,fs in facts.items() if fs}};found.append(spec)
    print('FOUND',p,q,a0,a1,flush=True)
    out.mkdir(exist_ok=True,parents=True);(out/f'fold-{p}-{q}.tm').write_text(encode(new));(out/f'fold-{p}-{q}.json').write_text(json.dumps(spec,indent=2)+'\n')
 print('DONE',len(found),'seconds',time.time()-started,flush=True)
 out.mkdir(exist_ok=True,parents=True);(out/'results.json').write_text(json.dumps({'folds':found,'seconds':time.time()-started},indent=2)+'\n')

if __name__=='__main__':search(read_table(sys.argv[1]),Path(sys.argv[2]))
