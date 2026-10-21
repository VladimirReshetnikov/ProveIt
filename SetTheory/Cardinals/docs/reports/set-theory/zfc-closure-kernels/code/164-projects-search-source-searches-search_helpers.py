import sys,json,collections,time,itertools,hashlib
from pathlib import Path
OUT=Path(__file__).resolve().parent.parent/"search-output"
OUT.mkdir(exist_ok=True)
sys.path.insert(0,str(Path(__file__).resolve().parent.parent/'vendor'));sys.path.insert(0,str(Path(__file__).resolve().parent.parent/'vendor'))
import source_language as s,build221 as b,source_splice as sp,global_allocator_v2 as alloc
base=(Path(__file__).resolve().parent.parent/'inputs');T=b.read_table((base/'k217.native.tm').read_bytes());old=s.tree(json.loads((base/'sites217.json').read_bytes()));G,P=b.decoder_map(T,old);basecfg=s.graph_intervals(s.sites(old))
spans=[]
def walk(n,p='',i=0):
 j=i+sp.size(n);spans.append((n,p,i,j))
 if not s.leaf(n):walk(n[0],p+'0',i);walk(n[1],p+'1',i+sp.size(n[0]))
walk(old)
allroles=set().union(*G.values());protected=set().union(*(ns for q,ns in G.items()if len(ns)>1));bytype=collections.defaultdict(list)
for n,p,i,j in spans:bytype[n].append((p,i,j))
pairs=json.load(open(Path(__file__).resolve().parent.parent/'results/helper-pairs.json'));pairs=[r for r in pairs if r['helpers']]
seen=set();res=[];count=0;start=time.monotonic();bests=[]
def assoc(xs,kind):
 if len(xs)==1:return xs[0]
 k=1 if kind=='right'else len(xs)-1 if kind=='left'else len(xs)//2
 return assoc(xs[:k],kind),assoc(xs[k:],kind)
for r in pairs:
 aa,bb=r['pair'];bit=r['bit'];tx,ty=r['targets']
 if bit==0:
  starts=list(G.get(tx,[]));ends=[n for q in G if q not in(aa,bb)and T[q,0]==T[bb,0]for n in G[q]]
 else:
  starts=[n for q in G if q not in(aa,bb)and T[q,1]==T[aa,1]for n in G[q]];ends=list(G.get(ty,[]))
 starts=[x for x in starts if s.boundary(x)==(0,0,False)];ends=[x for x in ends if s.boundary(x)==(0,0,False)]
 print('PAIR',aa,bb,bit,'starts',len(starts),'ends',len(ends),flush=True)
 for A,C in itertools.product(starts,ends):
  for (pa,lo,ae),(pc,cs,hi)in itertools.product(bytype[A],bytype[C]):
   if not ae<cs or hi-lo>700:continue
   try:middle=sp.closed_forest(old,ae,cs)
   except AssertionError:continue
   for kind in('right','left','balanced'):
    X=assoc(middle,kind);H=((A,X),C)if bit==0 else(A,(X,C))
    try:new=sp.apply_closed_splices(old,{(lo,hi):H})
    except AssertionError:continue
    if new in seen:continue
    seen.add(new);count+=1
    ns=sp.nodes(new);m=len(ns)
    if m>203 or not protected<=ns:continue
    met=sp.metrics(new)
    if met['maximum_zero_run']>6:continue
    ss=s.sites(new);assert s.graph_intervals(ss)==basecfg==s.graph_arithmetic(ss)[0]
    item={'pair':[aa,bb],'bit':bit,'span':[lo,hi],'kind':kind,'metrics':met};res.append(item)
    try:U,ar=alloc.compile_tree(s,b,T,old,new,protected_states=frozenset((aa,bb)))
    except Exception as e:item['allocation_error']=str(e);continue
    item['prefold_states']=ar['working_states']
    if ar['working_states']>217:continue
    GG,PP=b.decoder_map(U,new);hs=[q for q,ns in GG.items()if H in ns]
    for hq in hs:
     if U[hq,0][:2]!=(0,1)or U[hq,1][:2]!=(1,1):continue
     j,k=U[hq,0][2],U[hq,1][2]
     if U.get((j,bit))!=T[aa,bit]or U.get((k,bit))!=T[bb,bit]:continue
     inc=lambda q:[(p,v,w,d)for(p,v),(w,d,z)in U.items()if z==q]
     if not inc(aa)or not inc(bb)or any((w,d)!=(0,1)for p,v,w,d in inc(aa))or any((w,d)!=(1,1)for p,v,w,d in inc(bb)):continue
     V={(q,v):(w,d,aa if z==bb else z)for(q,v),(w,d,z)in U.items()if q!=bb};V[aa,bit]=(bit,-1,hq)
     try:VG,VP=b.decoder_map(V,new)
     except Exception as e:item['fold_error']=str(e);continue
     expect={q:set(ns)for q,ns in GG.items()};expect[aa]|=expect.pop(bb)
     if dict(VG)!=expect:continue
     item['fold_states']=len(V)//2;item['helper']=hq
     p=(OUT/f'helper-candidate{len(bests):03d}');p.with_suffix('.json').write_bytes(s.compact(ss));p.with_suffix('.tm').write_bytes(b.table_bytes(V));p.with_suffix('.receipt.json').write_text(json.dumps(item,indent=2)+'\n');bests.append(item);print('HIT',item,flush=True)
     if len(V)//2<=216:break
    if bests and bests[-1].get('fold_states',999)<=216:break
   if bests and bests[-1].get('fold_states',999)<=216:break
  if bests and bests[-1].get('fold_states',999)<=216:break
 if bests and bests[-1].get('fold_states',999)<=216:break
 if time.monotonic()-start>300:break
(OUT/'helper-search.json').write_text(json.dumps({'elapsed':time.monotonic()-start,'distinct_sources':count,'qualified':res,'hits':bests},indent=2)+'\n');print('DONE',count,len(res),bests,time.monotonic()-start,flush=True)
