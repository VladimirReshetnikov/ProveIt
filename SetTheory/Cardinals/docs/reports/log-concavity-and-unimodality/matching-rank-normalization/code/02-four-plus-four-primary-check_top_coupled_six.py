from itertools import combinations,combinations_with_replacement
from functools import lru_cache
from pathlib import Path
import json,hashlib
from support_counts import endpoints,norm,basis
Hs=[(0,0,1,2),(0,1,1,2),(0,1,2,3),(1,1,1,2),(1,1,2,2),(1,1,2,3),(1,2,3,4)]
ss4=list(combinations(range(6),4));ss3=list(combinations(range(6),3));ss2=list(combinations(range(6),2))
m4=[sum(1<<i for i in S) for S in ss4];m3=[sum(1<<i for i in S) for S in ss3]
qq=[(i,j) for i,x in enumerate(m4) for j,y in enumerate(m4) if x|y==63]
qh=[(i,j) for i,x in enumerate(m4) for j,y in enumerate(m3) if x|y==63]
part=[(i,ss3.index(tuple(j for j in range(6) if j not in S))) for i,S in enumerate(ss3) if 0 in S]
comp4=[ss4.index(tuple(k for k in range(6) if k not in S)) for S in ss2]
out=[]
for H in Hs:
 hb={(1<<i)|(1<<j) for i,j in combinations(range(4),2) if H[i] and H[j] and H[i]!=H[j]}
 good={(a,b):any(((1<<i)|(1<<j)) in hb for i in range(4) for j in range(4) if i!=j and a>>i&1 and b>>j&1) for a in range(16) for b in range(16)}
 be={(a,b):any((15^s) in hb for s in endpoints((a,b))) for a in range(1,16) for b in range(1,16)}
 hs=sum(1<<i for i in range(4) if H[i]);neg=[];least=10**9;sha=hashlib.sha256()
 for rows in combinations_with_replacement(range(1,16),6):
  Q4=[basis(tuple(rows[i] for i in S)) for S in ss4]
  N3=[norm(tuple(rows[i] for i in S)) for S in ss3]
  H3=[bool(n&hs) for n in N3]
  Q=sum(be[(rows[S[0]],rows[S[1]])] and Q4[ci] for S,ci in zip(ss2,comp4))
  D=sum(good[(N3[i],N3[j])] for i,j in part)
  Cqq=sum(Q4[i] and Q4[j] for i,j in qq)
  Cqh=sum(Q4[i] and H3[j] for i,j in qh)
  c=7*D+Cqq+Cqh-6*Q;least=min(least,c);sha.update(f'{rows}:{c}:{D}\n'.encode())
  if c<0:raise RuntimeError(('negative coefficient',H,rows,c,Q,D,Cqq,Cqh))
 out.append(dict(H=H,minimum=least,negative_count=len(neg),examples=neg[:10],sha256=sha.hexdigest()));print(out[-1],flush=True)
Path(__file__).with_suffix('.json').write_text(json.dumps(out,indent=2)+'\n')
