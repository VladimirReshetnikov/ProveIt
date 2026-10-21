from pathlib import Path
from functools import cache
import json,itertools,time
import source_language as s, source_splice as sp
P=Path(__file__).resolve().parent;ss=json.loads((P/'sites215.json').read_text());root=s.tree(ss)
ranges=[('G',479,888),('rho6',888,1171),('rho5',1171,1467),('rho4',1467,1766),('rho3',1766,2062),('rho2',2062,2412),('rho1',2412,2643)]
ps=list(itertools.permutations([3,4,5]))
def leafrow(i,n):
 if n[0]not in('CI','CD')or n[1]not in(3,4,5):return -1
 return next((k for k,(_,lo,hi)in enumerate(ranges)if lo<=i<hi),-1)
def annotate(n,i=0):
 if s.leaf(n):
  k=leafrow(i,n);return(n,k,None,None,0 if k<0 else 1<<k)
 a=annotate(n[0],i);b=annotate(n[1],i+sp.size(n[0]));return(n,-1,a,b,a[4]|b[4])
aroot=annotate(root)
fixed=[];forest=[[]for _ in ranges];cross=[]
def dec(an):
 n,k,a,b,mask=an
 if mask==0:fixed.append(n);return
 if mask&(mask-1)==0:
  forest[mask.bit_length()-1].append(an);return
 cross.append(n);dec(a);dec(b)
dec(aroot)
def tr(an,option):
 n,k,a,b,mask=an
 if s.leaf(n):
  return(n[0],dict(zip((3,4,5),ps[option]))[n[1]])if k>=0 else n
 return(tr(a,option),tr(b,option))
@cache
def shape(n):
 if s.leaf(n):return(n[0],99)if n[0]in('CI','CD')and n[1]in(3,4,5)else n
 return(shape(n[0]),shape(n[1]))
fixednodes=set().union(*(sp.nodes(n)for n in fixed));shapefixed={shape(n)for n in fixednodes}
shapeowned=set().union(*(sp.nodes(shape(an[0]))for f in forest for an in f))
shapecross=[shape(n)for n in cross]
assert len(set(shapecross))==len(cross),'Cross context shape collisions'
assert set(shapecross).isdisjoint(shapefixed|shapeowned),'Context may alias owned subtrees'
nodeids={n:i for i,n in enumerate(fixednodes)}
def mask(ns):
 x=0
 for n in ns:i=nodeids.setdefault(n,len(nodeids));x|=1<<i
 return x
base_mask=mask(fixednodes)
opts=[[mask(set().union(*(sp.nodes(tr(n,k))for n in f)))for k in range(6)]for f in forest]
basepred=base_mask
for o in opts:basepred|=o[0]
print('fixed',len(fixednodes),'cross',len(cross),'baselineexact',basepred.bit_count()+len(cross),'atoms',len(nodeids),flush=True)
assert basepred.bit_count()+len(cross)==202
best=1000;best_choices=[];count=0;start=time.time();hist={}
for choices in itertools.product(range(6),repeat=7):
 m=base_mask
 for k,ch in enumerate(choices):m|=opts[k][ch]
 score=m.bit_count()+len(cross);hist[score]=hist.get(score,0)+1
 if score<best:best=score;best_choices=[];print('BEST',best,choices,flush=True)
 if score==best:best_choices.append(choices)
 count+=1
results=[]
for ix,choices in enumerate(best_choices):
 rr=[list(z)for z in ss]
 for(_,lo,hi),ch in zip(ranges,choices):
  mp=dict(zip((3,4,5),ps[ch]))
  for i in range(lo,hi):
   if rr[i][1]in('CI','CD'):rr[i][2]=mp.get(rr[i][2],rr[i][2])
 m=s.metrics(s.tree(rr));assert m['dag_nodes']==best
 file=P/f'rowexact_{ix}_{best}.json';file.write_bytes(s.compact(rr));results.append({'choices':choices,'permutations':[ps[ch]for ch in choices],**m,'file':str(file)})
print('COMPLETE',count,'best',best,'bestvectors',len(best_choices),'secs',time.time()-start,flush=True)
(P/'row_permutation_exact_summary.json').write_text(json.dumps({'total_vectors':count,'method':'Exact fixed subtree union with dependency-one row forests and collision-excluded cross contexts','best':best,'histogram':hist,'cross_contexts':len(cross),'context_shape_uniqueness':True,'context_shape_disjointness':True,'results':results},indent=2)+'\n')

