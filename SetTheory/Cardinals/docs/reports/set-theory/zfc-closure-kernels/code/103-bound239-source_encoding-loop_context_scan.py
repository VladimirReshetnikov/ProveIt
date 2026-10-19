from pathlib import Path
from functools import cache
import json,collections,itertools
from loop_scan import S,I,R,N,D,ps,incregs,transfer,combine_incs,buildloop,cons,leaf,live,change
H=Path(__file__).resolve().parent
@cache
def boundary(n):
 x=S[n]
 if isinstance(x[0],str):return (1,0,False)if x[0]=='CD' else(x[1],0,False)if x[0]=='CB' else(0,x[1],False)if x[0]=='CC' else(0,0,x[0]=='CH')
 a,b=x;za,oa,ha=boundary(a);zb,ob,hb=boundary(b)
 return(max(max(za-1,0),zb),max(oa,max(ob-1,0)),ha or hb)
@cache
def closed(n):return boundary(n)==(0,0,False)
@cache
def word(n):
 x=S[n]
 if isinstance(x[0],int) and closed(x[0]) and closed(x[1]):return word(x[0])+word(x[1])
 return(n,)
byword=collections.defaultdict(list)
for n in range(N):
 if closed(n):byword[word(n)].append(n)

def assoc(xs):
 @cache
 def best(xs):
  if len(xs)==1:return (0,xs[0])
  if xs in byword:return(0,min(byword[xs]))
  choices=[]
  for i in range(1,len(xs)):
   ca,a=best(xs[:i]);cb,b=best(xs[i:]);choices.append((ca+cb+1,cons(a,b)))
  return min(choices)
 return best(tuple(xs))
base=live(R);out=[];seen=set()
for n in range(N):
 if not closed(n):continue
 ww=word(n)
 if len(ww)>18 or len(ww)<2:continue
 for j,w in enumerate(ww):
  tr=transfer(w)
  if not tr or not tr[1]:continue
  for k in range(1,len(tr[1])+1):
   for orient in ['after','before']:
    if orient=='after':other=ww[j+1:j+1+k];left,right=ww[:j],ww[j+1+k:]
    else:other=ww[max(0,j-k):j];left,right=ww[:max(0,j-k)],ww[j+1:]
    if len(other)!=k or any(S[t][0]!='CI' for t in other):continue
    ii=tuple(S[t][1]for t in other);r,body=tr
    if collections.Counter(ii)-collections.Counter(body):continue
    rest=list((collections.Counter(body)-collections.Counter(ii)).elements())
    for altW in buildloop(r,ii,rest):
     _,alt=assoc(left+(altW,)+right)
     key=(n,alt)
     if key in seen:continue
     seen.add(key);nr=change(n,alt);lv=live(nr);delta=len(lv)-len(base)
     item=dict(node=n,q=[q for q,v in D['qnodes'].items()if v==[n]],word=ww,j=j,orient=orient,r=r,body=body,extra=ii,rest=rest,alt=alt,delta=delta,newloop=altW,newloopnodes=[(x,S[x])for x in live(altW)if x>=N],leaves=len(ps(alt)),oldleaves=len(ps(n)))
     out.append(item)
     if delta<=1:print(item)
(H/'loop_context_results.json').write_text(json.dumps({'candidates':out,'structures':S},indent=2)+'\n');print('summary',collections.Counter(x['delta']for x in out),'total',len(out))
