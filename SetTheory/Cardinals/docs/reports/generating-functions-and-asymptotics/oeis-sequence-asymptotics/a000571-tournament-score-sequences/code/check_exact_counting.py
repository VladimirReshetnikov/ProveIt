from pathlib import Path
SCRIPT_DIR = Path(__file__).resolve().parent
RESULT_DIR = SCRIPT_DIR.parent / "results"
RESULT_DIR.mkdir(exist_ok=True)
"""Independent small-n Landau enumeration; no divisor recurrence for direct counts."""
from itertools import combinations_with_replacement
import math,json
M=10
phi=list(range(M+1))
for p in range(2,M+1):
 if phi[p]==p:
  for j in range(p,M+1,p):phi[j]-=phi[j]//p
N=[0]+[sum((-1)**(n+d)*phi[n//d]*math.comb(2*d,d) for d in range(1,n+1) if n%d==0)//(2*n) for n in range(1,M+1)]
S=[1];I=[0]
for n in range(1,M+1):
 S.append(sum(N[k]*S[n-k] for k in range(1,n+1))//n)
 I.append(S[n]-sum(I[k]*S[n-k] for k in range(1,n)))
rows=[]
for n in range(1,M+1):
 counts=[0]*(n+1)
 for seq in combinations_with_replacement(range(n),n):
  if sum(seq)!=n*(n-1)//2:continue
  total=0;parts=0;ok=True
  for j,v in enumerate(seq,1):
   total+=v;boundary=j*(j-1)//2
   if total<boundary:ok=False;break
   if total==boundary:parts+=1
  if ok:counts[parts]+=1
 assert sum(counts)==S[n]
 assert counts[1]==I[n]
 for u in [2,3,4]:
  w=[1]
  for j in range(1,n+1):w.append(u*sum(I[k]*w[j-k] for k in range(1,j+1)))
  assert w[n]==sum(counts[k]*u**k for k in range(1,n+1))
 rows.append({'n':n,'by_components':counts,'S':S[n],'I':I[n]})
print(json.dumps(rows,indent=2));open(str(RESULT_DIR / 'exact-counting-checks.json'),'w').write(json.dumps(rows,indent=2))
