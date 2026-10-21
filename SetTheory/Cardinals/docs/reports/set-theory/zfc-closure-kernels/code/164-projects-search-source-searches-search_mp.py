import sys,json,random,time,collections,functools
from pathlib import Path
OUT=Path(__file__).resolve().parent.parent/"search-output"
OUT.mkdir(exist_ok=True)
lib=Path(__file__).resolve().parent.parent/'vendor'
sys.path.insert(0,str(lib));import source_language as s,build221 as b
SRC=(Path(__file__).resolve().parent.parent/'inputs/dominated_yx205.json')
root0=s.tree(json.loads(SRC.read_text())); T=b.read_table((Path(__file__).resolve().parent.parent/'inputs/k217.native.tm').read_bytes())
G,P={},{}
N=[];lookup={}
def intern(a,b=None):
 key=a if b is None else(a,b)
 if key not in lookup:lookup[key]=len(N);N.append(key)
 return lookup[key]
def toid(n):return intern(n) if s.leaf(n) else intern(toid(n[0]),toid(n[1]))
def lf(n):return isinstance(N[n][0],str)
root=toid(root0)
protected=set()
print('MP-only closed rotations',flush=True)
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
def moves(r,reach):
 for n in reach-protected:
  if lf(n):continue
  a,c=N[n]
  if not lf(c):
   bb,cc=N[c]
   if all(closed(x)==(0,0,False)for x in(a,bb,cc)):
    yield n,intern(intern(a,bb),cc),'L'
  if not lf(a):
   aa,bb=N[a]
   if all(closed(x)==(0,0,False)for x in(aa,bb,c)):
    yield n,intern(aa,intern(bb,c)),'R'
start=time.monotonic();rng=random.Random(9327);best=205;steps=0;bestroot=root;seen={root};restarts=0
basecfg=s.graph_intervals(s.sites(root0));baseword=[x[1:]for x in s.sites(root0)]
duration=float(sys.argv[1]) if len(sys.argv)>1 else 420
while time.monotonic()-start<duration:
 reach,depth,z=infos(root);cand=[]
 for n,new,kind in moves(root,reach):
  rr=replace(root,n,new)
  if rr in seen:continue
  rch,d,zz=infos(rr)
  if protected<=rch and zz<=8 and d<=70:
   cand.append((len(rch)+max(0,zz-6),rr,n,new,kind,d));seen.add(rr)
 if not cand:
  root=toid(root0);restarts+=1;seen={root};continue
 m=min(x[0]for x in cand)
 if m<best:
  best=m;bestroot=next(x[1]for x in cand if x[0]==m)
  out=totr(bestroot);ss=s.sites(out);assert [x[1:]for x in ss]==baseword;assert s.graph_intervals(ss)==basecfg==s.graph_arithmetic(ss)[0]
  (OUT/f'mp-source{m}.json').write_bytes(s.compact(ss));print('NEW BEST',m,'step',steps,'seconds',time.monotonic()-start,'metrics',s.metrics(out),flush=True)
  if m<=202:break
 # Mostly greedy; plateau escapes up to 3 states.
 scores=[x for x in cand if x[0]<=min(m+1,206)]
 if not scores:
  root=toid(root0);restarts+=1;continue
 if rng.random()<.90:scores=[x for x in scores if x[0]==m]
 choice=rng.choice(scores);root=choice[1];steps+=1
 if steps%500==0:
  curtr=totr(root);besttr=totr(bestroot);prottr=[totr(n)for n in protected];N.clear();lookup.clear();closed.cache_clear();totr.cache_clear();toid(root0);root=toid(curtr);bestroot=toid(besttr);protected={toid(n)for n in prottr};seen={root}
 if steps%100==0:print('step',steps,'cost',choice[0],'min',best,'interned',len(N),'secs',round(time.monotonic()-start,1),flush=True)
print('DONE',best,steps,restarts,time.monotonic()-start,flush=True)
