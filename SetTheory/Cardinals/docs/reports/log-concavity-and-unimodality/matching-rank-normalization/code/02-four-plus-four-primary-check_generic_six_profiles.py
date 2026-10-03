from itertools import combinations,combinations_with_replacement
from pathlib import Path
from functools import lru_cache
import json,hashlib,time
masks=range(1,16)
@lru_cache(None)
def endpoints(rows):
 s={0}
 for row in rows:s={v|(1<<i) for v in s for i in range(4) if row>>i&1 and not v>>i&1}
 return s
@lru_cache(None)
def norm(rows):return sum(15^s for s in endpoints(rows))
@lru_cache(None)
def basis(rows):return 15 in endpoints(rows)
profiles=[(0,0,1,2),(0,1,1,2),(0,1,2,3),(1,1,1,2),(1,1,2,2),(1,1,2,3),(1,2,3,4)]
parts=[tuple(S) for S in combinations(range(6),3) if 0 in S]
subsets=list(combinations(range(6),2));out=[]
for H in profiles:
 hb={ (1<<i)|(1<<j) for i,j in combinations(range(4),2) if H[i] and H[j] and H[i]!=H[j]}
 beta={(a,b):any((15^s) in hb for s in endpoints((a,b))) for a in masks for b in masks}
 good={(a,b):any(((1<<i)|(1<<j)) in hb for i in range(4) for j in range(4) if i!=j and a>>i&1 and b>>j&1) for a in range(16) for b in range(16)}
 neg=[];least=100;counts={};sha=hashlib.sha256()
 for rows in combinations_with_replacement(masks,6):
  Q=sum(beta[(rows[i],rows[j])] and basis(tuple(rows[k] for k in range(6) if k not in (i,j))) for i,j in subsets)
  D=sum(good[(norm(tuple(rows[i] for i in S)),norm(tuple(rows[i] for i in range(6) if i not in S)))] for S in parts)
  c=Q-D;least=min(least,c);counts[c]=counts.get(c,0)+1;sha.update(f'{rows}:{c}\n'.encode())
  if c<0:raise RuntimeError(('negative coefficient',H,rows,Q,D))
 r=dict(H=H,profiles=sum(counts.values()),least=least,negative_count=len(neg),examples=neg[:20],coefficient_counts=counts,sha256=sha.hexdigest());out.append(r);print(r,flush=True)
Path(__file__).with_suffix('.json').write_text(json.dumps(out,indent=2)+'\n')
