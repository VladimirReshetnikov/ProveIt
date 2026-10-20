from row_permutations import *
from functools import cache
import collections,time
TREE,_,_=make({2:('a','c','b')})
OUT=ROOT/'rho6_row_order_results';OUT.mkdir(exist_ok=True)
INTERVALS=[(135,486),(486,895),(895,1178),(1178,1474),(1474,1773),(1773,2069),(2069,2419),(2419,2650)]
VALUES=[];IDS={};META=[];BOUND=[]
def intern(x):
 if x in IDS:return IDS[x]
 k=len(VALUES);IDS[x]=k;VALUES.append(x)
 if isinstance(x[0],str):META.append((1,0,0,0));BOUND.append(z.s.boundary(x))
 else:
  a,b=x;al,alead,az,ah=META[a];bl,blead,bz,bh=META[b]
  lead=1+alead;META.append((al+bl,lead,max(lead,az,bz),1+max(ah,bh)))
  aa,bb=BOUND[a],BOUND[b];BOUND.append((max(max(aa[0]-1,0),bb[0]),max(aa[1],max(bb[1]-1,0)),aa[2]or bb[2]))
 return k
@cache
def encode(t):return intern(t)if z.s.leaf(t)else intern(tuple(map(encode,t)))
RT=encode(TREE);assert len(VALUES)==206
ATOMS=[]
def template(k,lo=0):
 hi=lo+META[k][0];x=VALUES[k]
 if hi<=135 or lo>=2650:return('F',k)
 if 135<=lo and hi<=2650 and BOUND[k]==(0,0,False):
  if isinstance(x[0],str)or any(BOUND[c]!=(0,0,False)for c in x):
   i=len(ATOMS);ATOMS.append((lo,hi,k));return('A',i)
 assert not isinstance(x[0],str)
 return('N',template(x[0],lo),template(x[1],lo+META[x[0]][0]))
TEMPLATE=template(RT);ROWATOMS=[]
for lo,hi in INTERVALS:
 row=[k for a,b,k in ATOMS if lo<=a and b<=hi]
 assert sum(META[k][0]for k in row)==hi-lo;ROWATOMS.append(row)
BASE=(list(VALUES),dict(IDS),list(META),list(BOUND))
def reset():
 VALUES[:]=BASE[0];IDS.clear();IDS.update(BASE[1]);META[:]=BASE[2];BOUND[:]=BASE[3]
def compose_order(t,ats):
 if t[0]=='F':return t[1]
 if t[0]=='A':return ats[t[1]]
 return intern((compose_order(t[1],ats),compose_order(t[2],ats)))
def live(k):
 seen={k};todo=[k]
 for q in todo:
  x=VALUES[q]
  if isinstance(x[0],str):continue
  for c in x:
   if c not in seen:seen.add(c);todo.append(c)
 return seen
def decode(k):
 x=VALUES[k]
 return x if isinstance(x[0],str)else tuple(map(decode,x))

def main():
 best=206;hits=[];hist=collections.Counter();start=time.monotonic()
 for ix,order in enumerate(itertools.permutations(range(8))):
  ats=sum((ROWATOMS[i]for i in order),[]);q=compose_order(TEMPLATE,ats)
  met={'dag_nodes':len(live(q)),'leaf_occurrences':META[q][0],'maximum_zero_run':META[q][2],'maximum_depth':META[q][3]}
  hist[met['dag_nodes'],met['maximum_zero_run']]+=1
  if met['dag_nodes']<=206 and met['maximum_zero_run']<=6:
   r={'order':order,'names':[NAMES[i]for i in order],'metrics':met}
   if order!=tuple(range(8)) or ix==0:
    d=OUT/('_'.join(map(str,order)));d.mkdir(exist_ok=True);tt=decode(q);rr=z.s.sites(tt)
    assert z.s.metrics(tt)==met
    assert z.s.graph_arithmetic(rr)[0]==z.s.graph_intervals(rr)
    (d/'sites.json').write_bytes(z.s.compact(rr));r['sites_file']=str(d/'sites.json');hits.append(r);print(json.dumps(r),flush=True)
  best=min(best,met['dag_nodes'])
  if len(VALUES)>200000:reset()
  if ix and ix%10000==0:print('progress',ix,'best',best,'seconds',time.monotonic()-start,flush=True)
 result={'status':'EXHAUSTIVE_RHO6_ACB_ROW_ORDER_SOURCE_SCREEN','variants':40320,'best':best,'hits':hits,'histogram':[[a,b,n]for(a,b),n in sorted(hist.items())],'seconds':time.monotonic()-start}
 (OUT/'summary.json').write_text(json.dumps(result,indent=2)+'\n');print('complete',json.dumps(result),flush=True)
if __name__=='__main__':main()
