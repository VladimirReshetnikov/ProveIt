from pathlib import Path
from collections import defaultdict
from functools import lru_cache
import json,sys
sys.dont_write_bytecode=True
import search_directional as D
L=D.L

def proposals(t,root,allow_new=0):
 occ=defaultdict(set);incoming=defaultdict(list);seen=set()
 for(p,b),(w,d,z)in t.items():incoming[z].append((p,b,w,d))
 def pure(q):return(q,0)in t and all(t[q,b][:2]==(b,1)for b in(0,1))
 def visit(q,n):
  if(q,n)in seen:return
  seen.add((q,n));occ[q].add(n)
  if L.leaf(n):return
  for b in(0,1):
   w,d,z=t[q,b]
   if(w,d)==(b,1):visit(z,n[b])
 visit(84,root)
 out=[]
 for q,ns in occ.items():
  if q==84 or not pure(q)or any(L.leaf(n)for n in ns):continue
  ins=incoming[q]
  if not ins or len(set(p for p,b,w,d in ins))!=len(ins):continue
  if not all(p in occ and pure(p) and(w,d)==(b,1)for p,b,w,d in ins):continue
  parents={p:b for p,b,_,_ in ins};needed={};valid=True
  for p,side in parents.items():
   for n in occ[p]:
    if L.leaf(n)or L.leaf(n[side]):valid=False;break
    a,b,c=(*n[0],n[1])if side==0 else(n[0],*n[1])
    if L.boundary(a)[0]!=0 or L.boundary(c)[1]!=0:valid=False;break
   if not valid:break
   if side==0:a,b,c=t[q,0][2],t[q,1][2],t[p,1][2];pair=b,c
   else:a,b,c=t[p,0][2],t[q,0][2],t[q,1][2];pair=a,b
   needed[p]=pair
  if not valid:continue
  helpers={};missing=[]
  for pair in set(needed.values()):
   matches=[s for s in {s for s,b in t}if s!=q and s not in parents and t[s,0]==(0,1,pair[0])and t[s,1]==(1,1,pair[1])]
   if matches:helpers[pair]=min(matches)
   else:missing.append(pair)
  if len(missing)>allow_new:continue
  # For one missing pair, recycle the old q label: no net state cost.
  free=iter([q]+[x for x in range(226,254)if(x,0)not in t])
  for pair in missing:helpers[pair]=next(free)
  nt=dict(t)
  for p,side in parents.items():
   h=helpers[needed[p]]
   if side==0:nt[p,0]=(0,1,t[q,0][2]);nt[p,1]=(1,1,h)
   else:nt[p,0]=(0,1,h);nt[p,1]=(1,1,t[q,1][2])
  if missing:
   for pair in missing:
    h=helpers[pair];nt[h,0]=(0,1,pair[0]);nt[h,1]=(1,1,pair[1])
  else:nt={k:v for k,v in nt.items()if k[0]!=q}
  @lru_cache(None)
  def transform(s,n):
   if L.leaf(n):return n
   if s in parents:
    side=parents[s]
    if side==0:
     a=transform(t[q,0][2],n[0][0]);b=transform(t[q,1][2],n[0][1]);c=transform(t[s,1][2],n[1]);return(a,(b,c))
    a=transform(t[s,0][2],n[0]);b=transform(t[q,0][2],n[1][0]);c=transform(t[q,1][2],n[1][1]);return((a,b),c)
   ch=list(n)
   for bit in(0,1):
    w,d,z=t[s,bit]
    if(w,d)==(bit,1):ch[bit]=transform(z,ch[bit])
   return tuple(ch)
  nr=transform(84,root)
  out.append((q,parents,helpers,nt,nr))
 return out

if __name__=='__main__':
 b=D.I.base
 for cls,tp,sp in [('A',b/'machine/variant_plain/u208.native.tm',b/'machine/variant_plain/u208.sites.json'),('B',b/'machine/u208.native.tm',b/'machine/u208.sites.json')]:
  t=D.I.read(tp);ss=json.loads(sp.read_text());root=L.tree(ss);D.out=D.S.work/('shared_extended_'+cls);D.out.mkdir(exist_ok=True)
  props=[x for x in proposals(t,root,4)if len(x[1])>1];results=[]
  print('CLASS',cls,'proposals',len(props),flush=True)
  for i,(q,parents,helpers,nt,nr)in enumerate(props):
   if L.graph_intervals(L.sites(nr))!=L.graph_intervals(ss):raise ValueError('CFG changed')
   mt,folds=D.S.merge(nt)
   rec=D.test(mt,nr,[('shared',q,parents,str(helpers))],folds,i);results.append(rec)
  (D.out/'results.json').write_text(json.dumps(results,indent=2)+'\n')
