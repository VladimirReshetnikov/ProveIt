from analyze import *
import random,time,copy,argparse

# A source node stores its intended physical entry state explicitly.  Rotations
# change source parentheses and these intended state labels together.
def labeled(t,root):
 def walk(n,p,q):
  if c.leaf(n):return n
  out=[q]
  for b in (0,1):
   if c.leaf(n[b]):out.append(n[b]);continue
   mem={i:int(x)for i,x in enumerate(p+str(b))};mem[-1]=1;h=len(p);state=q
   for k in range(100):
    if h==len(p)+1:break
    w,d,state=t[state,mem[h]];mem[h]=w;h+=d
   out.append(walk(n[b],p+str(b),state))
  return tuple(out)
 return walk(root,'',84)

def ll(n):return isinstance(n[0],str)
@c.cache
def unlabel(n):return n if ll(n) else (unlabel(n[1]),unlabel(n[2]))

def check_mapping(t,root):
 visited=set(); qs=collections.defaultdict(set)
 def walk(n,p):
  if ll(n):return True
  key=(n,p[-8:])
  if key in visited:return True
  visited.add(key);q=n[0];qs[q].add(n)
  for b in (0,1):
   if ll(n[b+1]):continue
   mem={i:int(x)for i,x in enumerate(p+str(b))};mem[-1]=1;orig=mem.copy();h=len(p);state=q
   for k in range(100):
    if h==len(p)+1:break
    if h not in mem:return False
    w,d,state=t[state,mem[h]];mem[h]=w;h+=d
   if mem!=orig or h!=len(p)+1 or state!=n[b+1][0]:return False
   if not walk(n[b+1],p+str(b)):return False
  return True
 return qs if walk(root,'') else None

def collect(root):
 qs=collections.defaultdict(set);seen=set()
 def walk(n):
  if ll(n) or n in seen:return
  seen.add(n);qs[n[0]].add(n);walk(n[1]);walk(n[2])
 walk(root);return qs

def rotations(t,lr):
 qs=collect(lr);ports=collections.defaultdict(list)
 for (q,b),(w,d,z)in t.items():ports[z].append((q,b,w,d))
 out=[];bypair=collections.defaultdict(list)
 for s,ns in qs.items():
  if len(ns)==1 and all(t[s,b][:2]==(b,1)for b in(0,1)):
   sn=next(iter(ns));bypair[(sn[1],sn[2])].append(s)
 for q,ns in qs.items():
  if len(ns)!=1 or any(t[q,b][:2]!=(b,1)for b in (0,1)):continue
  n=next(iter(ns))
  for bit in (0,1):
   r=t[q,bit][2]
   if r not in qs or len(qs[r])!=1 or ll(n[bit+1]) or r!=n[bit+1][0]:continue
   if any(t[r,b][:2]!=(b,1)for b in (0,1)):continue
   child=n[bit+1]
   a,b,cc=(child[1],child[2],n[2])if bit==0 else(n[1],child[1],child[2])
   if any(c.boundary(unlabel(k))!=(0,0,False)for k in (a,b,cc)):continue
   if ports[r]==[(q,bit,bit,1)]:out.append((q,r,bit))
   pair=(b,cc)if bit==0 else(a,b)
   for s in bypair.get(pair,[]):
    if s not in(q,r):out.append((q,r,bit,s))
 return out

def rotate(t,lr,rot):
 q,r,bit=rot[:3];s=rot[3]if len(rot)>3 else r;ns=collect(lr)[q];assert len(ns)==1;n=next(iter(ns));child=n[bit+1]
 tt=t.copy()
 if bit==0:
  a,b,cc=child[1],child[2],n[2];nn=(q,a,(s,b,cc))
  ra=t[r,0][2];rb=t[r,1][2];qc=t[q,1][2]
  tt[q,0]=(0,1,ra);tt[q,1]=(1,1,s)
  if s==r:tt[r,0]=(0,1,rb);tt[r,1]=(1,1,qc)
 else:
  a,b,cc=n[1],child[1],child[2];nn=(q,(s,a,b),cc)
  qa=t[q,0][2];rb=t[r,0][2];rc=t[r,1][2]
  tt[q,0]=(0,1,s);tt[q,1]=(1,1,rc)
  if s==r:tt[r,0]=(0,1,qa);tt[r,1]=(1,1,rb)
 @c.cache
 def change(node):
  if node==n:return nn
  if ll(node):return node
  return(node[0],change(node[1]),change(node[2]))
 return tt,change(lr)

def folds(t):
 facts,_=v.bit_invariant(t,0,8)
 byaction=[collections.defaultdict(list),collections.defaultdict(list)]
 qs=sorted({q for q,b in t})
 for q in qs:
  if facts[q]is None:continue
  tag=facts[q].get(-1)
  if tag is None:continue
  for b in (0,1):byaction[tag][(b,t[q,b])].append(q)
 hs=[{},{}]
 for h in qs:
  if any(t[h,b][:2]!=(b,1)or t[h,b][2]==254 for b in (0,1)):continue
  z0=t[h,0][2];z1=t[h,1][2]
  for b in (0,1):
   for q0 in byaction[0].get((b,t[z0,b]),[]):
    for q1 in byaction[1].get((b,t[z1,b]),[]):
     if not ({h,z0,z1}&{q0,q1}):hs[b].setdefault((q0,q1),[]).append(h)
 hits=[]
 for q0,q1 in hs[0].keys()&hs[1].keys():
  if q0==0:continue
  for h0 in hs[0][q0,q1]:
   for h1 in hs[1][q0,q1]:
    if h0 not in(q0,q1)and h1 not in(q0,q1):hits.append((q0,q1,h0,h1))
 return hits,len(hs[0].keys()|hs[1].keys())

def encode(t):return ('#! start 0\n'+''.join(f'{q} {b} {w} {"R"if d==1 else"L"} {z}\n'for(q,b),(w,d,z)in sorted(t.items()))).encode()

if __name__=='__main__':
 ap=argparse.ArgumentParser();ap.add_argument('--iterations',type=int,default=5000);ap.add_argument('--seed',type=int,default=773);ap.add_argument('--basis',type=Path);a=ap.parse_args()
 if a.basis:
  t,_=v.parse_table((a.basis/'candidate225.klabels.tm').read_bytes());root=c.tree(json.loads((a.basis/'sites225.json').read_text()))
 rng=random.Random(a.seed);base=t;base_lr=labeled(t,root);lr=base_lr
 best=0;history=[];seen=set();accepted=0;tic=time.monotonic();out=Path(__file__).parent
 print('base rotations',rotations(t,lr),'base folds',folds(t),flush=True)
 for step in range(a.iterations):
  if step%50==0:t=base;lr=base_lr;history=[]
  rs=rotations(t,lr);rng.shuffle(rs);passed=False
  for rot in rs:
   tt,lrr=rotate(t,lr,rot);key=tuple(tt.items())
   if key in seen:continue
   seen.add(key)
   if check_mapping(tt,lrr)is None:continue
   metrics=c.metrics(unlabel(lrr))
   if metrics['maximum_zero_run']>6:continue
   t,lr=tt,lrr;history.append(rot);accepted+=1;passed=True;break
  if not passed:t=base;lr=base_lr;history=[];continue
  hits,score=folds(t)
  tableclasses=collections.defaultdict(list)
  for q in {q for q,b in t}:tableclasses[(t[q,0],t[q,1])].append(q)
  for group in tableclasses.values():
   if len(group)<2:continue
   q0,q1=sorted(group,reverse=True)[:2]
   if q0==0:q0,q1=q1,q0
   final={(q,b):(w,d,q1 if z==q0 else z)for(q,b),(w,d,z)in t.items()if q!=q0}
   proof=v.prove(t,final,0,0,q1,q0,0,None,8,65,20000)
   if proof['status'].startswith('PASS'):
    print('IDENTICAL_ROWS',step,history,(q0,q1),flush=True)
    stamp=f'hit_{a.seed}_{step}_{q0}_{q1}'
    (out/(stamp+'.tm')).write_bytes(encode(final));(out/(stamp+'_basis.tm')).write_bytes(encode(t))
    c.dump(out/(stamp+'_sites.json'),c.sites(unlabel(lr)));c.dump(out/(stamp+'_proof.json'),proof);c.dump(out/(stamp+'_history.json'),history)
    raise SystemExit
  if score>best:best=score;print('BEST',step,'score',best,'history',history,flush=True)
  if metrics['maximum_zero_run']<6:
   (out/'zero5.tm').write_bytes(encode(t));c.dump(out/'zero5_sites.json',c.sites(unlabel(lr)));c.dump(out/'zero5_history.json',history);print('ZERO5',history,flush=True)
  for q0,q1,h0,h1 in hits:
   final={(q,b):(w,d,q1 if z==q0 else z)for(q,b),(w,d,z)in t.items()if q!=q0}
   final[q1,0]=(0,-1,h0);final[q1,1]=(1,-1,h1)
   proof=v.prove(t,final,0,0,q1,q0,0,None,8,65,20000)
   if proof['status'].startswith('PASS'):
    print('HIT',step,history,(q0,q1,h0,h1),flush=True)
    stamp=f'hit_{a.seed}_{step}_{q0}_{q1}'
    (out/(stamp+'.tm')).write_bytes(encode(final));(out/(stamp+'_basis.tm')).write_bytes(encode(t))
    c.dump(out/(stamp+'_sites.json'),c.sites(unlabel(lr)));c.dump(out/(stamp+'_proof.json'),proof);c.dump(out/(stamp+'_history.json'),history)
    raise SystemExit
  if step%100==0:print('PROGRESS',step,'accepted',accepted,'secs',time.monotonic()-tic,flush=True)
 print('DONE',a.iterations,'accepted',accepted,'seen',len(seen),'secs',time.monotonic()-tic,flush=True)
