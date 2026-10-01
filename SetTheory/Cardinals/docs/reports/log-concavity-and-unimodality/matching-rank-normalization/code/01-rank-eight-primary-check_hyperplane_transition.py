from itertools import combinations,combinations_with_replacement
from pathlib import Path
import json,hashlib
from support_counts import endpoints,norm,basis
triples=list(combinations(range(5),3));out=[]
for H in (1,3,7,15):
 neg=[];least=100;counts={};sha=hashlib.sha256()
 for rows in combinations_with_replacement(range(1,16),5):
  Q=sum(bool(rows[i]&H) and basis(rows[:i]+rows[i+1:]) for i in range(5))
  S=0
  for J in triples:
   K=tuple(i for i in range(5) if i not in J)
   n=norm(tuple(rows[i] for i in J));pe=endpoints(tuple(rows[i] for i in K))
   S+=any((1<<i)|(1<<j) in pe for i in range(4) for j in range(4) if i!=j and n>>i&1 and H>>j&1)
  
  if 5*S<9*Q:raise RuntimeError(('nine-fifths failure',H,rows,S,Q))
  if S-2*Q<0 and (S,Q)!=(9,5):raise RuntimeError(('unexpected bad profile',H,rows,S,Q))
  c=S-2*Q;least=min(least,c);counts[c]=counts.get(c,0)+1;sha.update(f'{rows}:{c}\n'.encode())
  if c<0:neg.append((rows,c,S,Q))
 r=dict(normal_support=H,minimum=least,negative_count=len(neg),examples=neg[:20],counts=counts,sha256=sha.hexdigest());out.append(r);print(r,flush=True)
Path(__file__).with_suffix('.json').write_text(json.dumps(out,indent=2)+'\n')
