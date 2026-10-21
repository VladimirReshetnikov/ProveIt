from pathlib import Path
import sys,json,time,collections,functools
BASE=Path(__file__).resolve().parents[1]/'baseline/k215'
sys.path.insert(0,str(BASE/'code'));import source_language as s
R=s.tree(json.loads((BASE/'sites215.json').read_text()));ROWS=s.sites(R);G=s.graph_intervals(ROWS);N=len(ROWS)
@functools.lru_cache(None)
def size(n):return 1 if s.leaf(n) else size(n[0])+size(n[1])
@functools.lru_cache(None)
def node_set(n):return frozenset([n]) if s.leaf(n) else frozenset([n])|node_set(n[0])|node_set(n[1])
def repair(n,prefer=True):
 i=0;changes=[]
 def go(t,lo,zs,os):
  nonlocal i
  if s.leaf(t):
   op,a=t;target=G[lo][1]
   if op=='CD':
    if (zs[-1]%N if zs else 0)!=target[0]:raise ValueError('CD')
   elif op in ('CB','CC'):
    candidates=zs if op=='CB' else os;dest=target[0];opts=[j+1 for j,v in enumerate(reversed(candidates)) if v%N==dest]
    if dest==0:opts+=[len(candidates)+1]
    if not opts:raise ValueError(op)
    aa=a if prefer and a in opts else min(opts)
    if aa!=a:changes.append([lo,op,a,aa])
    t=(op,aa)
   return t
  mid=lo+size(t[0]);end=lo+size(t)
  return go(t[0],lo,zs+(end,),os),go(t[1],mid,zs,os+(lo,))
 return go(n,0,(),()),changes

def nodes(n,p=''):
 if s.leaf(n):return
 yield p,n
 yield from nodes(n[0],p+'0');yield from nodes(n[1],p+'1')

def replacements(n,which,r):
 if n==which:return r
 if s.leaf(n):return n
 return replacements(n[0],which,r),replacements(n[1],which,r)

out=Path(__file__).resolve().parent/'replay-open-results';out.mkdir(exist_ok=True)
best=202;stats=collections.Counter();found=[];started=time.monotonic();seen=set()
for p,n in nodes(R):
 if n in seen:continue
 seen.add(n)
 choices=[]
 if not s.leaf(n[0]):
  (a,b),c=n;choices.append(('right',(a,(b,c))))
 if not s.leaf(n[1]):
  a,(b,c)=n;choices.append(('left',((a,b),c)))
 for direction,nn in choices:
  cand=replacements(R,n,nn)
  for prefer in (True,False):
   stats['tried']+=1
   try:new,changes=repair(cand,prefer)
   except ValueError as e:stats['invalid_'+str(e)]+=1;continue
   st=len(node_set(new));stats['valid']+=1;stats['dag'+str(st)]+=1
   if st<=best and new!=R:
    key='candidate%04d'%len(found);(out/(key+'.json')).write_text(s.compact(s.sites(new)).decode());record={'key':key,'dag':st,'path':p,'direction':direction,'size':size(n),'prefer_original':prefer,'retags':changes};found.append(record);print(json.dumps(record),flush=True)
    assert s.graph_intervals(s.sites(new))==G
    if st<best:best=st
   node_set.cache_clear()
print(json.dumps({'stats':dict(stats),'best':best,'seconds':time.monotonic()-started,'found':len(found)}),flush=True)
(out/'summary.json').write_text(json.dumps({'stats':dict(stats),'best':best,'seconds':time.monotonic()-started,'found':found},indent=2))
