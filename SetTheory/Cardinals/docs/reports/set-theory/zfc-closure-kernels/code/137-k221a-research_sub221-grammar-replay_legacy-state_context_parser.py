"""K221-aware closed-word parser. Heuristic only; physical allocation/proofs separate."""
from pathlib import Path
import sys,json,itertools
from functools import cache
sys.path.insert(0,'research_sub224/theory');from source_utils import *
import fast_parser as fp
sys.path.insert(0,str(Path(__file__).resolve().parent));import compile221 as cc
@cache
def decode(n):
 x=cc.tr.nodes[n];return x if cc.tr.leaf(n)else tuple(decode(ch)for ch in x)
STATE={decode(n):q for n,q in cc.NQ.items()}
REQUIRED={}
for n,q in cc.NQ.items():
 mask=0
 for ctx in range(4):
  valid=True
  for b,child in enumerate(cc.tr.nodes[n]):
   if cc.tr.leaf(child):continue
   p=f'{ctx:02b}';mem={i-2:int(x)for i,x in enumerate(p)};mem[0]=b;orig=mem.copy();h=0;s=q
   for step in range(65):
    if h not in mem:valid=False;break
    w,d,s=cc.T[s,mem[h]];mem[h]=w;h+=d
    if h==1:
     valid &= s==cc.NQ[child] and mem==orig
     break
   else:valid=False
   if not valid:break
  if valid:mask|=1<<ctx
 REQUIRED[decode(n)]=mask
class StateParser(fp.Parser):
 def parse(self,tokens,beam=2,max_leading=5,context=2):
  for n in tokens:self.freeze(n)
  ctxroot=k.replace_all(c,fp.root,self.part,('CI',8));ctx=live(ctxroot)-{('CI',8)}
  ctxmask=sum(1<<q for q in cc.HELPQS)
  for n in ctx:
   if n in STATE:ctxmask|=1<<STATE[n]
  vals=self.base[:];ids={x:i for i,x in enumerate(vals)};masks=[];zs=[];ls=[];ds=[];good=[];trees=[]
  def metadata(x,q):
   if isinstance(x[0],str):return 0,0,0,0,15,x
   a,b=x;t=(trees[a],trees[b]);ok=REQUIRED.get(t,15)
   for ctx in range(4):
    if not (good[a]>>(2*(ctx%2))&1 and good[b]>>(2*(ctx%2)+1)&1):ok&=~(1<<ctx)
   bit=STATE.get(t,256+q)
   return masks[a]|masks[b]|(1<<bit),max(1+ls[a],zs[a],zs[b]),1+ls[a],1+max(ds[a],ds[b]),ok,t
  for q,x in enumerate(vals):
   m,z,l,d,g,t=metadata(x,q);masks.append(m);zs.append(z);ls.append(l);ds.append(d);good.append(g);trees.append(t)
  def intern(a,b):
   x=a,b
   if x not in ids:
    q=len(vals);ids[x]=q;vals.append(x);m,z,l,d,g,t=metadata(x,q);masks.append(m);zs.append(z);ls.append(l);ds.append(d);good.append(g);trees.append(t)
   return ids[x]
  def score(q):return (masks[q]&~ctxmask).bit_count(),zs[q],ds[q]
  tokenids=[self.bi[t]for t in tokens];dp={};fparts=[flat(t)for t in tokens];nf=len(tokens)
  for length in range(1,nf+1):
   for i in range(nf-length+1):
    j=i+length;f=tuple(y for x in fparts[i:j]for y in x);known=set(self.known.get(f,[]))
    if j==nf:known.update(self.tailknown.get(f,[]))
    if length==1:known.add(tokenids[i])
    for ctx in range(4):
     choices={q for q in known if good[q]>>ctx&1}
     for p in range(i+1,j):
      for a,b in itertools.product(dp[i,p,2*(ctx%2)],dp[p,j,2*(ctx%2)+1]):
       if max(1+ls[a],zs[a],zs[b])<=6:
        q=intern(a,b)
        if good[q]>>ctx&1:choices.add(q)
     if i==0 and j==nf:choices={q for q in choices if ls[q]<=max_leading}
     dp[i,j,ctx]=sorted(choices,key=score)[:beam]
  return [(score(q),trees[q])for q in dp[0,nf,context]],len(vals)
