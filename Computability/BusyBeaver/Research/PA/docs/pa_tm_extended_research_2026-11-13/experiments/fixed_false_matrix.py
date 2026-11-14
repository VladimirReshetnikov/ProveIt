from itertools import product
import json
from pathlib import Path
results=[]
for n in [2,3]:
 for dtuple in [tuple(range(1,n)),(n-1,)]:
  D=set(dtuple)
  count=0
  for vals in product(range(n),repeat=n*n):
   def I(x,y):return vals[x*n+y]
   if any(I(0,p) not in D for p in range(n)):continue
   if any(x in D and I(x,y) in D and y not in D for x in range(n) for y in range(n)):continue
   if any(I(I(I(p,0),r),I(I(r,p),I(s,p))) not in D for p,r,s in product(range(n),repeat=3)):continue
   count+=1
   witnesses=[]
   for p,q,r in product(range(n),repeat=3):
    if I(p,I(q,p)) not in D:witnesses.append(('K',p,q))
    if I(I(p,I(q,r)),I(I(p,q),I(p,r))) not in D:witnesses.append(('S',p,q,r))
    if I(I(I(p,q),p),p) not in D:witnesses.append(('P',p,q))
   if witnesses:
    out={'n':n,'D':list(D),'table':vals,'witnesses':witnesses}
    print(json.dumps(out),flush=True);results.append(out);break
  print(n,D,'models',count,'countermodels',len(results),flush=True)
Path(__file__).with_name('fixed_false_matrix_results.json').write_text(json.dumps(results,indent=2))
