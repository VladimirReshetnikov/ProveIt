from pathlib import Path
from window_base import read,write,abstract
from history_search import histories
from itertools import combinations,product
import json,time,sys
P=Path(__file__).resolve().parent

def path(T,q,cells,ban,limit,first=None):
 h=0;t=dict(cells);out=set();seen=set()
 for k in range(limit):
  if h not in t or(q,t[h])not in T:break
  conf=(q,h,tuple(sorted(t.items())))
  if conf in seen:break
  seen.add(conf)
  w,d,z=first if k==0 and first is not None else T[q,t[h]]
  t[h]=w;h+=d;q=z
  if q in ban:break
  out.add((q,h,tuple(sorted(t.items()))))
  if q==254:break
 return out

def search(T,name,r=3,limit=16,initial_only=False):
 I=abstract(T,r); hs,_=histories(T,12)
 for q in I:
  I[q]=[v for v in I[q]if any(all(not -r<=x<=r or ((v>>(x+r))&1)==b for x,b in c.items())for c in hs[q])]
 Q=sorted({q for q,b in T});actions=list(product((0,1),(-1,1),Q+[254]));trials=0;start=time.time()
 pairs_iter=[(q,0)for q in Q if q!=0]if initial_only else combinations([q for q in Q if q!=0],2)
 for index,(a,c)in enumerate(pairs_iter):
  ban={a,c};chosen=[]
  for b in(0,1):
   contexts=[]
   for q in(a,c):
    for v in I[q]:
     if(v>>r)&1!=b:continue
     cells=tuple((i-r,(v>>i)&1)for i in range(2*r+1));ends=path(T,q,cells,ban,limit)
     if not ends:break
     contexts.append((q,cells,ends))
    else:continue
    break
   else:
    opts=[z for z in actions if z[2]not in ban]
    contexts.sort(key=lambda x:len(x[2]))
    for q,cells,ends in contexts:
     nxt=[]
     for z in opts:
      trials+=1
      if path(T,c,cells,ban,limit,z)&ends:nxt.append(z)
     opts=nxt
     if not opts:break
    if opts:chosen.append(opts[0]);continue
   break
  if len(chosen)==2:
   C={(q,b):(w,d,c if z==a else z)for(q,b),(w,d,z)in T.items()if q!=a}
   C[c,0],C[c,1]=chosen
   out=P/f'{name}_two_{a}_{c}.tm';write(C,out)
   receipt={'input':name,'removed':a,'representative':c,'rows':chosen,'radius':r,'limit':limit,'pairs':index+1,'trials':trials,'seconds':time.time()-start};(out.with_suffix('.json')).write_text(json.dumps(receipt,indent=2));print('FOUND',receipt,flush=True);return receipt
  if index%1000==0:print(name,index,trials,round(time.time()-start,1),flush=True)
 result={'input':name,'found':False,'pairs':index+1,'trials':trials,'seconds':time.time()-start,'radius':r,'limit':limit};print('DONE',result,flush=True);return result
if __name__=='__main__':
 result=search(read(Path(sys.argv[1])),sys.argv[2],r=4,limit=32,initial_only=True)
 (P/(sys.argv[2]+"_results.json")).write_text(json.dumps(result,indent=2))
