from itertools import combinations,combinations_with_replacement,permutations
from functools import lru_cache
from pathlib import Path
from random import Random
import json,hashlib
from support_counts import endpoints,norm,basis
Hs=[(0,0,1,2),(0,1,1,2),(0,1,2,3),(1,1,1,2),(1,1,2,2),(1,1,2,3),(1,2,3,4)]
ss4=list(combinations(range(5),4));ss3=list(combinations(range(5),3));ss2=list(combinations(range(5),2))
m4=[sum(1<<i for i in S) for S in ss4];m3=[sum(1<<i for i in S) for S in ss3];m2=[sum(1<<i for i in S) for S in ss2]
qh=[(i,j) for i,x in enumerate(m4) for j,y in enumerate(m3) if x|y==31]
qb=[(i,j) for i,x in enumerate(m4) for j,y in enumerate(m2) if x|y==31]
parts=[(i,j) for i,x in enumerate(m3) for j,y in enumerate(m3) if i<j and x|y==31]
rng=Random(54042026);values=[[rng.randrange(1,101) for j in range(4)] for i in range(5)]
def det3(a):return a[0][0]*(a[1][1]*a[2][2]-a[1][2]*a[2][1])-a[0][1]*(a[1][0]*a[2][2]-a[1][2]*a[2][0])+a[0][2]*(a[1][0]*a[2][1]-a[1][1]*a[2][0])
def cofactor(vs):return tuple((-1)**j*det3([v[:j]+v[j+1:] for v in vs]) for j in range(4))
cache=[]
for rows in combinations_with_replacement(range(1,16),5):
 Q4=[basis(tuple(rows[i] for i in S)) for S in ss4]
 N3=[norm(tuple(rows[i] for i in S)) for S in ss3]
 vv=[tuple(values[i][j] if row>>j&1 else 0 for j in range(4)) for i,row in enumerate(rows)]
 normals=[cofactor([vv[i] for i in S]) for S in ss3]
 cache.append((rows,Q4,N3,normals))
out=[]
for H in Hs:
 hb={(1<<i)|(1<<j) for i,j in combinations(range(4),2) if H[i] and H[j] and H[i]!=H[j]}
 be={(a,b):any((15^s) in hb for s in endpoints((a,b))) for a in range(1,16) for b in range(1,16)}
 hs=sum(1<<i for i in range(4) if H[i]);neg=[];least=10**9;sha=hashlib.sha256()
 for rows,Q4,N3,normals in cache:
  H3=[bool(n&hs) for n in N3];B2=[be[(rows[S[0]],rows[S[1]])] for S in ss2]
  q=sum(Q4);Cqq=q*(q-1);Cqh=sum(Q4[i] and H3[j] for i,j in qh);Q=sum(Q4[i] and B2[j] for i,j in qb)
  res=[(sum(n[i] for i in range(4) if H[i]),sum(n[i]*H[i] for i in range(4))) for n in normals]
  D=sum(res[i][0]*res[j][1]-res[i][1]*res[j][0]!=0 for i,j in parts)
  c=7*D+Cqq+Cqh-6*Q;least=min(least,c);sha.update(f'{rows}:{c}:{D}\n'.encode())
  if c<0:raise RuntimeError(('negative coefficient',H,rows,c,Q,D,Cqq,Cqh))
 out.append(dict(H=H,profiles=len(cache),minimum=least,negative_count=len(neg),examples=neg[:15],sha256=sha.hexdigest()));print(out[-1],flush=True)
Path(__file__).with_suffix('.json').write_text(json.dumps(dict(values=values,results=out),indent=2)+'\n')
