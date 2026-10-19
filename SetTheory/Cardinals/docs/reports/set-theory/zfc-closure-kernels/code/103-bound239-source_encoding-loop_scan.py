from pathlib import Path
from functools import cache
import json,collections,itertools
H=Path(__file__).resolve().parent;D=json.loads((H/'mapping.json').read_text());S=[tuple(x)for x in D['structures']];I={x:n for n,x in enumerate(S)};R=D['pathnode'][''];N=len(S)
def cons(a,b):
 x=(a,b)
 if x not in I:I[x]=len(S);S.append(x)
 return I[x]
def leaf(op,r):
 x=(op,r)
 if x not in I:I[x]=len(S);S.append(x)
 return I[x]
@cache
def ps(n):
 x=S[n]
 if isinstance(x[0],str):return (('',x[0],x[1]),)
 return tuple((str(b)+p,o,r) for b in(0,1) for p,o,r in ps(x[b]))
@cache
def incregs(n):
 p=ps(n)
 return tuple(r for _,o,r in p) if all(o=='CI' for _,o,_ in p) else None
@cache
def transfer(n):
 p=ps(n)
 if len(p)<2 or p[0][0]!='0' or p[0][1]!='CD':return None
 r=p[0][2];body=p[1:-1];end=p[-1]
 if end[1]!='CC' or end[2]!=end[0].count('1'):return None
 if any(o!='CI' or v==r for pp,o,v in body):return None
 return (r,tuple(v for pp,o,v in body))
def combine_incs(incs):
 # all binary parenthesizations for at most4inc leaves
 if len(incs)==1:return [leaf('CI',incs[0])]
 return list({cons(a,b)for i in range(1,len(incs))for a in combine_incs(incs[:i])for b in combine_incs(incs[i:])})
def buildloop(r,prefix,rest):
 # Build valid repeat prefix; dec r; rest; CC
 if not rest:
  return [cons(A,cons(leaf('CD',r),leaf('CC',2)))for A in combine_incs(prefix)]
 return [cons(A,cons(leaf('CD',r),cons(B,leaf('CC',3))))for A in combine_incs(prefix)for B in combine_incs(rest)]
def live(root):
 seen=set();todo=[root]
 while todo:
  n=todo.pop()
  if n in seen:continue
  seen.add(n)
  if isinstance(S[n][0],int):todo.extend(S[n])
 return seen
baselive=live(R)
def change(n,alt):
 @cache
 def f(k):
  if k==n:return alt
  if isinstance(S[k][0],str):return k
  return cons(f(S[k][0]),f(S[k][1]))
 return f(R)
print('transfers',[(n,transfer(n))for n in range(N)if transfer(n)])
results=[]
for n in range(N):
 x=S[n]
 if isinstance(x[0],str):continue
 for orient in(0,1):
  w,a=x[orient],x[1-orient];tr=transfer(w);ii=incregs(a)
  if not tr or not ii:continue
  r,body=tr
  if collections.Counter(ii)-collections.Counter(body):continue
  rest=list((collections.Counter(body)-collections.Counter(ii)).elements())
  for alt in buildloop(r,ii,rest):
   nr=change(n,alt);l=live(nr);item=dict(node=n,sourceq=[q for q,v in D['qnodes'].items()if v==[n]],orient=orient,transfer_node=w,transferq=[q for q,v in D['qnodes'].items()if v==[w]],r=r,body=body,extra=ii,rest=rest,alternative=alt,total=len(l),delta=len(l)-len(baselive),local_nodes_new=[(j,S[j]) for j in live(alt) if j>=N])
   results.append(item);print(item)
(H/'loop_scan_results.json').write_text(json.dumps({'candidates':results,'structures':S},indent=2)+'\n')
