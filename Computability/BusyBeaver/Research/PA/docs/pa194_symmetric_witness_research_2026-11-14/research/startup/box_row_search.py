from explore import *
from append_search import encode,decode,sim
import random,itertools,time
T=parse(BASE/'pa194.native.tm')
T={(q,b):(w,d,88 if n==301 else n) for(q,b),(w,d,n)in T.items()if q!=301};T[88,0]=(0,False,51);T[51,0]=(0,True,122)

def testcase(tab,op,vs,r):
 if op=='mark':
  q=sr.SK[r];ip=encode(vs);end=1 if r==0 else 3;hgoal=-1
 elif op=='inc':q=64;ip=encode(vs,r);end=40;hgoal=-1
 else:q=0;ip=encode(vs,r);end=97 if vs[r]==0 else 40;hgoal=-1 if vs[r]==0 else 0
 out=sim(tab,q,0,ip,lambda q,h,o:q==end and h==hgoal,5000)
 if out is None:return None
 q,h,ones,n=out
 if op=='mark':
  expect=encode(vs,r)
  return ([],n)if ones==expect else None
 offset=int(op=='dec' and vs[r]>0)
 if offset and 0 not in ones:return None
 decoded=decode({x-offset for x in ones if x>=offset})
 expected=list(vs);expected[r]+=1 if op=='inc' else -int(op=='dec'and vs[r]>0)
 if decoded is None or len(decoded)<10 or decoded[:9]!=expected[:9]:return None
 return decoded,n

rng=random.Random(17024)
cases=[('inc',[0]*10,0),('dec',[0]*10,0),('dec',[1]*10,0)]+[(op,[rng.randrange(4)for _ in range(rng.randrange(10,15))],rng.randrange(9))for _ in range(15)for op in['inc','dec','mark']]
base=T.copy();candidates=[];start=time.time()
for changed_q in [0,64,74,94,66,198,113,16,40,54,97]:
 for bit in[0,1]:
  row=(changed_q,bit)
  local=[]
  for target in sorted({q for q,b in T}):
   for w,d in itertools.product([0,1],[False,True]):
    a=(w,d,target)
    if a==base[row]:continue
    T[row]=a;res=[]
    for op,vs,r in cases:
     out=testcase(T,op,vs,r)
     if out is None:break
     res.append(out)
    else:
     local.append({'row':row,'action':a,'examples':res[:3]})
  T[row]=base[row]
  print(row,len(local),flush=True);candidates+=local
summary={'seconds':time.time()-start,'candidates':candidates}
(BASE/'box_row_search.json').write_text(json.dumps(summary,indent=2));print('done',summary['seconds'],len(candidates),flush=True)
