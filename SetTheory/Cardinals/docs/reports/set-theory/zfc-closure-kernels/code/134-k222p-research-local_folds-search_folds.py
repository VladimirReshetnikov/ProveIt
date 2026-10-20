from pathlib import Path
import sys,json,itertools,time,collections

def load(p):
 t={}
 for ln in Path(p).read_text().splitlines():
  if ln and not ln.startswith('#'):
   q,b,w,d,z=ln.split();t[int(q),int(b)]=(int(w),1 if d=='R' else -1,int(z))
 return t

def facts(t,r=8,start=0):
 qs={q for q,b in t}; ff={start:{}}; todo=collections.deque([start])
 while todo:
  q=todo.popleft();old=ff[q]
  for b in (0,1):
   if old.get(0,b)!=b:continue
   w,d,z=t[q,b]
   if z not in qs:continue
   new={k-d:v for k,v in old.items() if -r<=k-d<=r};new[-d]=w
   if z in ff:new={k:v for k,v in new.items() if ff[z].get(k)==v}
   if z not in ff or ff[z]!=new:ff[z]=new;todo.append(z)
 return {q:ff.get(q,{}) for q in qs}

def good(t,entry,init,target,limit=20,exception=None):
 q,h=entry,0;tape=dict(init); z,eh,expect=target; seen=set()
 for i in range(limit):
  if h not in tape or (q,tape[h]) not in t:return False
  w,d,q=t[q,tape[h]];tape[h]=w;h+=d
  if q==z and h==eh and tape==expect:return True
 return False

def first_action(t,act,init,target,limit=20):
 tape=dict(init);w,h,q=act;tape[0]=w;z,eh,expect=target
 trace=set()
 for i in range(limit):
  if q==z and h==eh and tape==expect:return trace
  if h not in tape or (q,tape[h]) not in t:return None
  trace.add(q)
  w,d,q=t[q,tape[h]];tape[h]=w;h+=d
 return None

def search(path,outdir):
 t=load(path);qs=sorted({q for q,b in t});ff=facts(t)
 outdir=Path(outdir);outdir.mkdir(exist_ok=True)
 Path(outdir/'facts.json').write_text(json.dumps(ff,indent=2))
 actions=list(itertools.product((0,1),(-1,1),qs)); allowed={}; count=0
 for q in qs:
  for b in (0,1):
   if ff[q].get(0,b)!=b:allowed[q,b]=None;continue
   ini={**ff[q],0:b};w,d,z=t[q,b];ex={**ini,0:w}
   a={}
   for act in actions:
    trace=first_action(t,act,ini,(z,d,ex))
    if trace is not None:a[act]=trace
   allowed[q,b]=a;count+=len(a)
 print(path,'rewrite rows',count,'facts',sum(map(len,ff.values())),flush=True)
 found=[]
 for keep,drop in itertools.combinations([q for q in qs if q!=0],2):
  if any(t[q,b][2] in (keep,drop) for q in (keep,drop) for b in (0,1)):continue
  sets=[]
  for b in (0,1):
   p=allowed[keep,b];d=allowed[drop,b]
   if p is None and d is None:a=[(b,1,keep)]
   else:
    u=set(p) if d is None else set(d) if p is None else set(p)&set(d)
    a=[act for act in u if not ({keep,drop}&((p.get(act,set()) if p else set())|(d.get(act,set()) if d else set())))]
   sets.append(a)
  if not all(sets):continue
  for a0,a1 in itertools.product(*sets):
   ph=lambda q:keep if q==drop else q
   nt={(q,b):(w,d,ph(z)) for (q,b),(w,d,z) in t.items() if q!=drop}
   nt[keep,0]=(a0[0],a0[1],ph(a0[2]));nt[keep,1]=(a1[0],a1[1],ph(a1[2]))
   ok=True
   for q in (keep,drop):
    for b in (0,1):
     if ff[q].get(0,b)!=b:continue
     ini={**ff[q],0:b};w,d,z=t[q,b];ex={**ini,0:w}
     if not good(nt,keep,ini,(ph(z),d,ex)):ok=False;break
   if ok:
    item=dict(keep=keep,delete=drop,a0=a0,a1=a1)
    print('FOLD FOUND',item,flush=True);found.append(item)
    Path(outdir/f'{keep}_{drop}.tm').write_text('#! start 0\n'+''.join(f'{q} {b} {w} {"R" if d==1 else "L"} {z}\n' for (q,b),(w,d,z) in sorted(nt.items())))
    break
 Path(outdir/'folds.json').write_text(json.dumps(found,indent=2))
 print('FINISHED',len(found),flush=True)

if __name__=='__main__':search(sys.argv[1],sys.argv[2])
