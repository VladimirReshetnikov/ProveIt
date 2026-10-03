from collections import defaultdict
from itertools import combinations
from math import factorial
import kernel as K
N=12
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
def es(ids,k):return plus(*(mono(c)for c in combinations(ids,k)))
def core(rows):
 f=K.features(rows)
 return {(k,j):plus(*(mono(list(K.IDX[S])+[5+i for i in K.IDX[J]])for z,(kk,jj,S,J)in enumerate(K.PAIRS)if kk==k and jj==j and f[z]))for k in range(1,6)for j in range(min(k,5-k)+1)}
def reduced(rows,strong=True):
 C=core(rows);X=plus(mono([10]),mono([11]));Y=plus(mono([10,11],2),mono([11,11]));Z=plus(mono([10,11,11],3),mono([11,11,11]))
 g1=plus(C[1,1],mul(C[1,0],X));g2=plus(scale(C[2,2],2),scale(mul(C[2,1],X),2),mul(C[2,0],Y));g3=plus(scale(mul(C[3,2],X),6),scale(mul(C[3,1],Y),3),mul(C[3,0],Z))
 p=plus(mul(g2,g2),scale(mul(g1,g3),-2))if strong else plus(scale(mul(g2,g2),3),scale(mul(g1,g3),-4))
 return [g1,g2,g3],p
