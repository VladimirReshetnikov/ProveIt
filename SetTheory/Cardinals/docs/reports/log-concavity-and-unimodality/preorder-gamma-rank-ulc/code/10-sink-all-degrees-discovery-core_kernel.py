from itertools import permutations,combinations
from collections import defaultdict
from math import prod
N=10
Z=(0,)*N

def mono(ids,c=1):
 e=[0]*N
 for i in ids:e[i]+=1
 return {tuple(e):c}
def plus(*ps):
 out=defaultdict(int)
 for p in ps:
  for e,c in p.items():out[e]+=c
 return {e:c for e,c in out.items()if c}
def scale(p,a):return {e:a*c for e,c in p.items()if a*c}
def mul(p,q):
 out=defaultdict(int)
 for e,c in p.items():
  for f,d in q.items():out[tuple(a+b for a,b in zip(e,f))]+=c*d
 return {e:c for e,c in out.items()if c}
def es(indices,k):return plus(*(mono(c)for c in combinations(indices,k)))

def core_polys(rows):
 a=plus(*(mono([i,4+j])for i in range(4)for j in range(4)if rows[i]>>j&1))
 c=plus(*(mono(list(S)+[4+j])for j in range(4)for S in combinations([i for i in range(4)if i!=j],2)if any(rows[i]>>j&1 for i in S)))
 d=plus(*(mono([i for i in range(4)if i!=j]+[4+j])for j in range(4)if any(rows[i]>>j&1 for i in range(4))))
 b={}
 for j,k in combinations(range(4),2):
  S=[i for i in range(4)if i not in [j,k]]
  if (rows[S[0]]>>j&1 and rows[S[1]]>>k&1)or(rows[S[1]]>>j&1 and rows[S[0]]>>k&1):b=plus(b,mono(S+[4+j,4+k]))
 return a,b,c,d

def reduced(rows):
 a,b,c,d=core_polys(rows)
 e1,e2,q=[es(range(4),k)for k in [1,2,3]]
 X=plus(mono([8]),mono([9]));twoY=plus(mono([8,9],2),mono([9,9]));sixZ=plus(mono([8,9,9],3),mono([9,9,9]))
 g1=plus(a,mul(e1,X));g2=plus(scale(b,2),scale(mul(c,X),2),mul(e2,twoY));g3=plus(scale(mul(d,twoY),3),mul(q,sixZ))
 p=plus(scale(mul(g2,g2),2),scale(mul(g1,g3),-3))
 return [g1,g2,g3],p

def canonical(rows):
 return min(tuple(sum(1<<j for j in range(4)if rows[perm[i]]>>perm[j]&1)for i in range(4))for perm in permutations(range(4)))
def is_preorder(rows):
 R=[rows[i]|1<<i for i in range(4)]
 return all(not(R[i]>>j&1)or(R[j]&~R[i])==0 for i in range(4)for j in range(4))
def cores():
 edges=[(i,j)for i in range(4)for j in range(4)if i!=j]
 reps=set()
 for code in range(4096):
  r=tuple(sum(1<<j for k,(i0,j)in enumerate(edges)if i==i0 and code>>k&1)for i in range(4))
  reps.add(canonical(r))
 return sorted(reps)
if __name__=='__main__':
 import json
 reps=cores();summary=[]
 for i,r in enumerate(reps):
  g,p=reduced(r);summary.append({'id':i,'rows':r,'preorder':is_preorder(r),'terms':len(p),'negative':sum(c<0 for c in p.values())})
 print(json.dumps({'classes':len(reps),'preorder_classes':sum(x['preorder']for x in summary),'coefficientwise_positive':sum(x['negative']==0 for x in summary),'targets':summary},indent=2))
