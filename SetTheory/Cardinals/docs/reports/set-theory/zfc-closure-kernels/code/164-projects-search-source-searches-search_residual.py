import sys,json,random,time,collections,functools
from pathlib import Path
HERE=Path(__file__).resolve().parent.parent
sys.path.insert(0,str(HERE/'vendor'))
sys.path.insert(0,str(HERE/'vendor'))
import source_language as s,build221 as b,global_allocator_v2 as alloc
SRC=Path(sys.argv[1]);out=Path(sys.argv[2]);out.mkdir(exist_ok=True);duration=float(sys.argv[3])if len(sys.argv)>3 else 180
root0=s.tree(json.loads(SRC.read_bytes()));T=b.read_table((Path(__file__).resolve().parent.parent/'inputs/k217.native.tm').read_bytes());OLD=s.tree(json.loads((Path(__file__).resolve().parent.parent/'inputs/sites217.json').read_bytes()))
N=[];lookup={}
def intern(a,b=None):
 key=a if b is None else(a,b)
 if key not in lookup:lookup[key]=len(N);N.append(key)
 return lookup[key]
def toid(n):return intern(n)if s.leaf(n)else intern(toid(n[0]),toid(n[1]))
def lf(n):return isinstance(N[n][0],str)
root=toid(root0);protected=set()
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
   if all(closed(x)==(0,0,False)for x in(a,bb,cc)):yield n,intern(intern(a,bb),cc),'L'
  if not lf(a):
   aa,bb=N[a]
   if all(closed(x)==(0,0,False)for x in(aa,bb,c)):yield n,intern(aa,intern(bb,c)),'R'
reach,depth,zero=infos(root)
if len(sys.argv)>4 and sys.argv[4]=='protect':
 G,P=b.decoder_map(T,OLD)
 protected={toid(n)for q,nn in G.items()if len(nn)>1 for n in nn};protected &= reach
 print('Protected',len(protected),flush=True)
rng=random.Random(983271);start=time.monotonic();best=999;bestphysical=999;steps=0;bestroot=root;seen={root};restarts=0;written=set();basecfg=s.graph_intervals(s.sites(root0));baseword=[x[1:]for x in s.sites(root0)];price_errors=collections.Counter()
def save(rr,score):
 global bestphysical
 tree=totr(rr);ss=s.sites(tree);assert [x[1:]for x in ss]==baseword;assert s.graph_intervals(ss)==basecfg==s.graph_arithmetic(ss)[0]
 if score not in written:
  (out/f'source{score}.json').write_bytes(s.compact(ss));written.add(score)
 try:
  tt,receipt=alloc.compile_tree(s,b,T,OLD,tree,hypothetical_entries=False,require_pure_rows=True)
  pp=receipt['working_states']
  if pp<bestphysical:
   bestphysical=pp;(out/f'physical{pp}.json').write_bytes(s.compact(ss));(out/f'physical{pp}.native.tm').write_bytes(b.table_bytes(tt));(out/f'physical{pp}.allocation.json').write_text(json.dumps(receipt,indent=2)+'\n');print('PHYSICAL',pp,s.metrics(tree),flush=True)
 except Exception as ex:price_errors[str(ex)[:110]]+=1
while time.monotonic()-start<duration:
 reach,depth,z=infos(root);score=len(reach)+max(0,z-6)
 if score<best:
  best=score;bestroot=root;save(root,best);print('BEST',best,'step',steps,'secs',round(time.monotonic()-start,2),'metrics',s.metrics(totr(root)),flush=True)
 if steps%70==0:save(root,score)
 cand=[]
 for n,new,kind in moves(root,reach):
  rr=replace(root,n,new)
  if rr in seen:continue
  rch,d,zz=infos(rr)
  if protected<=rch and zz<=8 and d<=65:cand.append((len(rch)+max(0,zz-6),rr,n,new,kind,d));seen.add(rr)
 if not cand:
  root=bestroot if rng.random()<.5 else toid(root0);restarts+=1;seen={root};continue
 m=min(x[0]for x in cand);scores=[x for x in cand if x[0]<=min(m+1,best+3)]
 if not scores:
  root=bestroot if rng.random()<.5 else toid(root0);restarts+=1;continue
 if rng.random()<.88:scores=[x for x in scores if x[0]==m]
 choice=rng.choice(scores);root=choice[1];steps+=1
 if steps%500==0:
  curtr=totr(root);besttr=totr(bestroot);prottr=[totr(n)for n in protected];N.clear();lookup.clear();closed.cache_clear();totr.cache_clear();toid(root0);root=toid(curtr);bestroot=toid(besttr);protected={toid(n)for n in prottr};seen={root}
print('DONE',best,bestphysical,steps,restarts,round(time.monotonic()-start,2),'errors',dict(price_errors),flush=True)
(out/'search-receipt.json').write_text(json.dumps(dict(best_score=best,best_physical=bestphysical,steps=steps,restarts=restarts,seconds=time.monotonic()-start,errors=dict(price_errors)),indent=2)+'\n')
