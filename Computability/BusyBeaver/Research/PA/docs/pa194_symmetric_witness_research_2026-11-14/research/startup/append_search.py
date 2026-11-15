from explore import *
import random,itertools,time
T=parse(BASE/'pa194.native.tm')
T={(q,b):(w,d,88 if n==301 else n) for(q,b),(w,d,n)in T.items()if q!=301};T[88,0]=(0,False,51);T[51,0]=(0,True,122)

def encode(vs,mark=None):
 out=set();h=0
 for i,v in enumerate(vs):
  out.update(range(h+1+(i==mark),h+v+2));h+=v+2
 return out

def decode(ones):
 if not ones or min(ones)<0:return None
 vs=[];h=0
 while h<max(ones):
  if h in ones or h+1 not in ones:return None
  v=0;h+=1
  while h in ones:h+=1;v+=1
  vs.append(v-1)
 return vs

def sim(T,q,h,ones,stop,fuel=10000):
 ones=set(ones);lo=min(ones)if ones else 0;hi=max(ones)if ones else 0
 for i in range(fuel):
  if i and stop(q,h,ones):return q,h,ones,i
  if (q,0)not in T:return None
  b=int(h in ones);w,d,n=T[q,b];dr=1 if d else -1
  if n==q and not b and ((dr==1 and h>hi)or(dr==-1 and h<lo)):return None
  if w:ones.add(h);lo=min(lo,h);hi=max(hi,h)
  else:ones.discard(h)
  q,h=n,h+dr
 return None

def test_action(a,vs,r):
 tab=dict(T);tab[198,0]=a
 out=sim(tab,64,0,encode(vs,r),lambda q,h,o:q==40 and h==-1,20000)
 if out is None:return None
 q,h,ones,n=out;decoded=decode(ones)
 expected=list(vs);expected[r]+=1
 if decoded is None or len(decoded)<10 or decoded[:9]!=expected[:9]:return None
 return decoded,n

if __name__=='__main__':
 rng=random.Random(17024)
 cases=[([0]*10,r)for r in[0,8,4]]+[([rng.randrange(4)for _ in range(rng.randrange(10,15))],rng.randrange(9))for _ in range(20)]
 candidates=[];start=time.time()
 for q in sorted({q for q,b in T}):
  for w,d in itertools.product([0,1],[False,True]):
   a=(w,d,q);res=[]
   for vs,r in cases:
    out=test_action(a,vs,r)
    if out is None:break
    res.append(out)
   else:candidates.append({'action':a,'results':res})
 print(json.dumps({'seconds':time.time()-start,'candidates':candidates},indent=2))
 (BASE/'append_search.json').write_text(json.dumps({'seconds':time.time()-start,'candidates':candidates},indent=2))
