"""Closed reassociation search with a literal backward-route projection objective."""
from pathlib import Path
from functools import cache
from collections import Counter
import json,sys,time
H=Path(__file__).resolve().parent;J=json.loads((H/'boundary_success.json').read_text());OLD=json.loads((H/'mapping.json').read_text())['structures'];raw=J['structures']
S=[tuple(x) for x in OLD];I={v:n for n,v in enumerate(S)}
def cons(a,b):
 v=a,b
 if v not in I:I[v]=len(S);S.append(v)
 return I[v]
@cache
def norm(n):
 x=raw[n]
 if isinstance(x[0],str):return I[tuple(x)]
 return cons(norm(x[0]),norm(x[1]))
R=norm(J['root']);N0=len(S)
def live(n):
 seen=set();todo=[n]
 while todo:
  k=todo.pop()
  if k in seen:continue
  seen.add(k)
  if isinstance(S[k][0],int):todo.extend(S[k])
 return seen
@cache
def boundary(n):
 x=S[n]
 if isinstance(x[0],str):return (1,0,False) if x[0]=='CD' else (x[1],0,False) if x[0]=='CB' else (0,x[1],False) if x[0]=='CC' else (0,0,x[0]=='CH')
 a,b=map(boundary,x);return(max(max(a[0]-1,0),b[0]),max(a[1],max(b[1]-1,0)),a[2] or b[2])
def closed(n):return boundary(n)==(0,0,False)
@cache
def lead(n):return 1+lead(S[n][0]) if isinstance(S[n][0],int) else 0
@cache
def zr(n):return max(1+lead(S[n][0]),zr(S[n][0]),zr(S[n][1])) if isinstance(S[n][0],int) else 0
@cache
def depth(n):return 1+max(map(depth,S[n])) if isinstance(S[n][0],int) else 0
TARGETS={(a,b) for a in (67,88,83) for b in (78,95,103,126,146)}

@cache
def fingerprint(n):
 x=S[n]
 if isinstance(x[0],str):return ({'CI':1,'CD':2,'CB':3,'CC':4,'CH':5}[x[0]]*20+(x[1] or 0)+1,1)
 a,la=fingerprint(x[0]);b,lb=fingerprint(x[1]);return ((a*pow(257,lb,2**128)+b)%(2**128),la+lb)
BASEQ={n:int(q) for q,ns in json.loads((H/'mapping.json').read_text())['qnodes'].items() for n in ns}
FPQ={fingerprint(n):q for n,q in BASEQ.items()}
ALIASES={fingerprint(n) for q,ns in json.loads((H/'mapping.json').read_text())['qnodes'].items() if len(ns)>1 for n in ns}
# The q243 projection through q244/188/220 requires the exact source100 split.
REQUIRED={99,100}
def score(root):
 L=live(root);hits=[n for n in L if S[n] in TARGETS];qs=set();fresh=0;fps=set()
 for n in L:
  if isinstance(S[n][0],str):continue
  fp=fingerprint(n);fps.add(fp)
  if fp in FPQ:qs.add(FPQ[fp])
  else:fresh+=1
 missing=len(ALIASES-fps)+len(REQUIRED-L)
 return 50+len(qs)+fresh,len(L),zr(root),depth(root),missing,hits

def replace(root,n,alt):
 @cache
 def f(k):
  if k==n:return alt
  if isinstance(S[k][0],str):return k
  return cons(*map(f,S[k]))
 return f(root)

def candidates(root):
 for n in sorted(live(root)):
  x=S[n]
  if isinstance(x[0],str):continue
  a,b=x
  if isinstance(S[b][0],int):
   b,c=S[b]
   if all(map(closed,(a,b,c))):yield n,cons(cons(a,b),c),'left',(a,b,c)
  a,c=x
  if isinstance(S[a][0],int):
   a,b=S[a]
   if all(map(closed,(a,b,c))):yield n,cons(a,cons(b,c)),'right',(a,b,c)

width=int(sys.argv[1]) if len(sys.argv)>1 else 160
limit=int(sys.argv[2]) if len(sys.argv)>2 else 15
nodecap=int(sys.argv[3]) if len(sys.argv)>3 else 225
began=time.time();beam=[];seen=set();history=[]
for n,alt,d,chunks in candidates(R):
 nr=replace(R,n,alt);sc=score(nr)
 if sc[-1] and sc[0]<=240 and sc[2]<=6 and sc[4]==0:beam.append((nr,[dict(node=n,alternative=alt,direction=d,chunks=chunks)]));seen.add(nr);print('SEED',sc,beam[-1][1],flush=True)
print('seeds',len(beam),'baseline',score(R),flush=True)
for step in range(limit):
 new=[];examined=0
 for root,hist in beam:
  for n,alt,d,chunks in candidates(root):
   nr=replace(root,n,alt)
   if nr in seen:continue
   seen.add(nr);sc=score(nr);examined+=1
   if sc[0]>240 or sc[2]>6 or not sc[-1] or sc[4]:continue
   nh=hist+[dict(node=n,alternative=alt,direction=d,chunks=chunks)]
   if sc[0]<=239:
    result=dict(status='SOURCE_ONLY_FOUND',root=nr,original_root=R,structures=S,history=nh,score=sc,target_pairs=sorted(TARGETS),seconds=time.time()-began,width=width,depth=step+1)
    (H/'projection_guarded_success.json').write_text(json.dumps(result,indent=2)+'\n');print('FOUND',sc,nh,flush=True);sys.exit(0)
   new.append(((sc[0],sc[1],sc[3]),nr,nh))
 new.sort(key=lambda x:(x[0],x[1]));beam=[(nr,h) for sc,nr,h in new[:width]]
 print('step',step+1,'examined',examined,'retained',len(new),'beam',len(beam),'best',[x[0] for x in new[:3]],'seconds',round(time.time()-began,2),flush=True)
 history.append(dict(depth=step+1,examined=examined,retained=len(new),best=new[0][0] if new else None))
 if not beam:break
 keep=set(range(N0))
 for nr,h in beam:
  keep.update(live(nr))
  for m in h:
   for v in [m['node'],m['alternative'],*m['chunks']]:keep.update(live(v))
 mp={old:new for new,old in enumerate(sorted(keep))}
 S2=[tuple(mp[a] for a in S[n]) if isinstance(S[n][0],int) else S[n] for n in sorted(keep)]
 beam=[(mp[nr],[dict(node=mp[m['node']],alternative=mp[m['alternative']],direction=m['direction'],chunks=tuple(mp[x] for x in m['chunks'])) for m in h]) for nr,h in beam]
 S[:]=S2;I.clear();I.update({v:n for n,v in enumerate(S)});seen={nr for nr,h in beam}
 for f in (boundary,lead,zr,depth,fingerprint):f.cache_clear()
 nr,h=beam[0];(H/'projection_guarded_checkpoint.json').write_text(json.dumps(dict(status='SOURCE_ONLY_225_NODE',root=nr,original_root=R,structures=S,history=h,score=score(nr),step=step+1),indent=2)+'\n')
(H/'projection_guarded_negative.json').write_text(json.dumps(dict(status='BOUNDED_SEARCH_NO_HIT',width=width,depth=step+1,nodecap=nodecap,seconds=time.time()-began,layers=history),indent=2)+'\n')
