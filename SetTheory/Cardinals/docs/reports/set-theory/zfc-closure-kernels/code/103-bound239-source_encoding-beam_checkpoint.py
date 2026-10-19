from pathlib import Path
from functools import cache
from collections import Counter
import json,time,heapq,sys
H=Path(__file__).resolve().parent
D=json.loads((H/'mapping.json').read_text());S=[tuple(x) for x in D['structures']];I={v:n for n,v in enumerate(S)};R=D['pathnode'][''];N0=len(S)

def cons(a,b):
 v=(a,b)
 if v not in I:I[v]=len(S);S.append(v)
 return I[v]
def live(n):
 seen=set();todo=[n]
 while todo:
  k=todo.pop()
  if k in seen:continue
  seen.add(k)
  if isinstance(S[k][0],int):todo.extend(S[k])
 return seen
@cache
def closed(n):
 x=S[n]
 if isinstance(x[0],str):return x[0]=='CI'
 # conservative exact syntactic boundary via zero/one availability
 return boundary(n)==(0,0,False)
@cache
def boundary(n):
 x=S[n]
 if isinstance(x[0],str):
  return (1,0,False) if x[0]=='CD' else (x[1],0,False) if x[0]=='CB' else (0,x[1],False) if x[0]=='CC' else (0,0,x[0]=='CH')
 z0,o0,h0=boundary(x[0]);z1,o1,h1=boundary(x[1]);return(max(max(z0-1,0),z1),max(o0,max(o1-1,0)),h0 or h1)
@cache
def lead(n):return 1+lead(S[n][0]) if isinstance(S[n][0],int) else 0
@cache
def zr(n):
 return max(1+lead(S[n][0]),zr(S[n][0]),zr(S[n][1])) if isinstance(S[n][0],int) else 0
@cache
def depth(n):return 1+max(depth(S[n][0]),depth(S[n][1])) if isinstance(S[n][0],int) else 0

def replace(root,n,alt):
 @cache
 def f(k):
  if k==n:return alt
  if isinstance(S[k][0],str):return k
  a,b=S[k];na,nb=f(a),f(b)
  return cons(na,nb)
 return f(root)

def candidates(root):
 for n in live(root):
  x=S[n]
  if isinstance(x[0],str):continue
  a,b=x
  if isinstance(S[b][0],int):
   b,c=S[b]
   if closed(a) and closed(b) and closed(c):yield n,cons(cons(a,b),c),'L',(a,b,c)
  a,c=x
  if isinstance(S[a][0],int):
   a,b=S[a]
   if closed(a) and closed(b) and closed(c):yield n,cons(a,cons(b,c)),'R',(a,b,c)

@cache
def leafcount(n):return leafcount(S[n][0])+leafcount(S[n][1]) if isinstance(S[n][0],int) else 1
@cache
def bad(n,k):
 if k>=7:return leafcount(n)
 if isinstance(S[n][0],str):return 0
 return bad(S[n][0],k+1)+bad(S[n][1],0)
def score(root):return len(live(root)),zr(root),bad(root,0),depth(root)
seed=replace(R,69,cons(88,67))
beam=[(seed,[dict(node=69,alternative=cons(88,67),direction='L',chunks=(56,60,67))])];seen={seed};width=int(sys.argv[1]) if len(sys.argv)>1 else 100;limit=int(sys.argv[2]) if len(sys.argv)>2 else 8
started=time.time();best=[]
for step in range(limit):
 new=[];num=0
 for root,hist in beam:
  for n,alt,d,chunks in candidates(root):
   nr=replace(root,n,alt)
   if nr in seen:continue
   seen.add(nr);sc=score(nr);num+=1
   if sc[0]>224 or sc[1]>7:continue
   nh=hist+[dict(node=n,alternative=alt,direction=d,chunks=chunks)]
   if sc[0]<225 and sc[1]<=6:
    print('FOUND',step+1,sc,nh,flush=True)
    (H/'beam3_success.json').write_text(json.dumps({'original_root':R,'root':nr,'structures':S,'history':nh,'score':sc},indent=2)+'\n');sys.exit()
   new.append((sc,nr,nh))
 new.sort(key=lambda x:(x[0],x[1]))
 beam=[(nr,h) for sc,nr,h in new[:width]]
 print('step',step+1,'examined',num,'retained',len(new),'beam',len(beam),'best',[(x[0],x[1]) for x in new[:3]],'secs',round(time.time()-started,2),'nodes',len(S),flush=True)
 if not beam:break
 # Compact global hashcons storage after every beam level, retaining history data.
 keep=set(range(N0))
 for nr,h in beam:
  keep.update(live(nr))
  for move in h:
   for v in [move['node'],move['alternative'],*move['chunks']]:keep.update(live(v))
 mapping={old:new for new,old in enumerate(sorted(keep))}
 S2=[tuple(mapping[a] for a in S[n]) if isinstance(S[n][0],int) else S[n] for n in sorted(keep)]
 beam=[(mapping[nr],[dict(node=mapping[m['node']],alternative=mapping[m['alternative']],direction=m['direction'],chunks=tuple(mapping[x] for x in m['chunks'])) for m in h]) for nr,h in beam]
 S[:]=S2;I.clear();I.update({v:n for n,v in enumerate(S)});seen={nr for nr,h in beam}
 for f in (lead,zr,depth,boundary,closed,leafcount,bad):f.cache_clear()
 nr,h=beam[0]
 (H/'beam_checkpoint.json').write_text(json.dumps(dict(original_root=R,root=nr,structures=S,history=h,score=score(nr),step=step+1),indent=2)+'\n')
(H/'beam3_negative.json').write_text(json.dumps({'width':width,'depth':step+1,'seen':len(seen),'secs':time.time()-started,'best':[(sc,h) for sc,n,h in new[:10]]},indent=2)+'\n')
