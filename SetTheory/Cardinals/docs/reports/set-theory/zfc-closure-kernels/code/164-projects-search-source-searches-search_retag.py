import sys,json,random,time,collections,functools
from pathlib import Path
OUT=Path(__file__).resolve().parent.parent/"search-output"
OUT.mkdir(exist_ok=True)
lib=Path(__file__).resolve().parent.parent/'vendor'
sys.path.insert(0,str(lib));import source_language as s,build221 as b
SRC=(Path(__file__).resolve().parent.parent/'inputs/sites217.json')
root0=s.tree(json.loads(SRC.read_text())); T=b.read_table((Path(__file__).resolve().parent.parent/'inputs/k217.native.tm').read_bytes())
G,P=b.decoder_map(T,root0)
N=[];lookup={}
def intern(a,b=None):
 key=a if b is None else(a,b)
 if key not in lookup:lookup[key]=len(N);N.append(key)
 return lookup[key]
def toid(n):return intern(n) if s.leaf(n) else intern(toid(n[0]),toid(n[1]))
def lf(n):return isinstance(N[n][0],str)
root=toid(root0)
protected={toid(n) for q in (69,213,90,92) for n in G[q]}
print('protected',protected,[(q,len(G[q]),P[q][:5])for q in(69,213,90,92)],flush=True)
@functools.cache
def closed(n):
 if lf(n):
  o,a=N[n];return (1,0,False)if o=='CD'else(a,0,False)if o=='CB'else(0,a,False)if o=='CC'else(0,0,o=='CH')
 l,r=map(closed,N[n]);return(max(l[0]-1,r[0],0),max(l[1],r[1]-1,0),l[2]or r[2])
@functools.cache
def totr(n):return N[n]if lf(n)else tuple(map(totr,N[n]))
def infos(r):
 reach=set();depth={};zeros={};leftz={}
 def go(n):
  if n in reach:return
  reach.add(n)
  if lf(n):depth[n]=zeros[n]=leftz[n]=0
  else:
   a,c=N[n];go(a);go(c);depth[n]=1+max(depth[a],depth[c]);leftz[n]=1+leftz[a];zeros[n]=max(leftz[n],zeros[a],zeros[c])
 go(r);return reach,depth[r],zeros[r]
def replace(r,old,new):
 cache={}
 def go(n):
  if n==old:return new
  if lf(n):return n
  if n in cache:return cache[n]
  a,c=N[n];aa,cc=go(a),go(c);cache[n]=intern(aa,cc);return cache[n]
 return go(r)
@functools.cache
def size(n):return 1 if lf(n) else sum(size(c)for c in N[n])
@functools.cache
def sem(n):
 out=[]
 def go(q,i,zs,os):
  if lf(q):
   o,a=N[q]
   if o in('CD','CB'):
    aa=1 if o=='CD'else a;v=zs[-aa]if aa<=len(zs)else('ext',aa-len(zs))
   elif o=='CC':v=os[-a]if a<=len(os)else('ext',a-len(os))
   else:v=None
   out.append((o,a,v));return
  a,c=N[q];go(a,i,zs+[i+size(q)],os);go(c,i+size(a),zs,os+[i])
 go(n,0,[],[]);return tuple(out)
@functools.cache
def rotate(n,d):
 a,c=N[n]
 if d=='L':
  if lf(c):return None
  bb,cc=N[c];r=intern(intern(a,bb),cc)
 else:
  if lf(a):return None
  aa,bb=N[a];r=intern(aa,intern(bb,c))
 old=sem(n)
 def go(q,i,zs,os):
  if lf(q):
   o,a,v=old[i]
   if o in('CD','CB','CC'):
    ar=zs if o in('CD','CB')else os
    if isinstance(v,tuple):aa=len(ar)+v[1]
    else:
     if v not in ar:raise ValueError
     aa=1+ar[::-1].index(v)
    if o=='CD':
     actual=ar[-1]if ar else('ext',1)
     if actual!=v:raise ValueError
    else:
     if o=='CB'and aa!=1:raise ValueError
     if o=='CC'and aa>3:raise ValueError
     a=aa
   return intern((o,a))
  a,c=N[q];return intern(go(a,i,zs+[i+size(q)],os),go(c,i+size(a),zs,os+[i]))
 try:return go(r,0,[],[])
 except ValueError:return None
@functools.cache
def badinfo(n):
 if lf(n):return ((1,0,0,0,0,0),0)
 lh,lb=badinfo(N[n][0]);rh,rb=badinfo(N[n][1]);return ((sum(rh),*lh[:5]),lb+rb+lh[5])
def moves(r,reach):
 for n in reach-protected:
  if lf(n):continue
  for d in('L','R'):
   rr=rotate(n,d)
   if rr is not None:yield n,rr,d
start=time.monotonic();rng=random.Random(77019);best=204;steps=0;bestroot=root;seen={root};restarts=0
basecfg=s.graph_intervals(s.sites(root0));baseword=[x[1:]for x in s.sites(root0)]
duration=float(sys.argv[1]) if len(sys.argv)>1 else 420
while time.monotonic()-start<duration:
 reach,depth,z=infos(root);cand=[]
 for n,new,kind in moves(root,reach):
  rr=replace(root,n,new)
  if rr in seen:continue
  rch,d,zz=infos(rr)
  if protected<=rch and zz<=6 and d<=70:
   cand.append((len(rch)+badinfo(rr)[1]/1000,rr,n,new,kind,d));seen.add(rr)
 if not cand:
  root=toid(root0);restarts+=1;seen={root};continue
 m=min(x[0]for x in cand)
 if m<best:
  best=m;bestroot=next(x[1]for x in cand if x[0]==m)
  out=totr(bestroot);ss=s.sites(out);assert s.graph_intervals(ss)==basecfg==s.graph_arithmetic(ss)[0]
  (OUT/f'retag-source{m:.3f}.json').write_bytes(s.compact(ss));print('NEW BEST',m,'step',steps,'seconds',time.monotonic()-start,'metrics',s.metrics(out),flush=True)
  if m<203 or (m==203 and s.metrics(out)['maximum_zero_run']<=5):break
 # Mostly greedy; plateau escapes up to 3 states.
 scores=[x for x in cand if x[0]<=min(m+1,206)]
 if not scores:
  root=toid(root0);restarts+=1;continue
 if rng.random()<.90:scores=[x for x in scores if x[0]==m]
 choice=rng.choice(scores);root=choice[1];steps+=1
 if steps%500==0:
  curtr=totr(root);besttr=totr(bestroot);prottr=[totr(n)for n in protected];N.clear();lookup.clear();closed.cache_clear();totr.cache_clear();size.cache_clear();sem.cache_clear();rotate.cache_clear();badinfo.cache_clear();toid(root0);root=toid(curtr);bestroot=toid(besttr);protected={toid(n)for n in prottr};seen={root}
 if steps%100==0:print('step',steps,'cost',choice[0],'min',best,'interned',len(N),'secs',round(time.monotonic()-start,1),flush=True)
print('DONE',best,steps,restarts,time.monotonic()-start,flush=True)
