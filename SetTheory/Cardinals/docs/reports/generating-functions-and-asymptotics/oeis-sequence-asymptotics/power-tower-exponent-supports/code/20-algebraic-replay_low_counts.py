"""Exact congruence-product and counting checks; standard library only."""
from math import gcd,isqrt
from pathlib import Path
import json
records=[]
for q in range(2,19):
 for p in range((q+1)//2,q):
  if 2*p<q or gcd(p,q)!=1:continue
  C=(q-p)*(2*p+q)
  for r,t in [(2,3),(3,1)]:
   def num(L):return t*L*L+p*L-2*p*p*r+p*q-q*q
   roots=[]
   for L in range(p*C):
    v=num(L)
    if v%C:continue
    N=v//C
    if (L+(2*p-q)*N-2*p*r+q)%p==0:roots.append(L)
   h1=sum(num(L)%C==0 for L in range(C))
   h2=sum((t*y*y-y-2)%p==0 for y in range(p))
   if len(roots)!=h1*h2 or not roots:raise RuntimeError(('CRT count',p,q,r))
   # At modest cutoffs compare the true integer equations with residue filtering.
   direct=0;congruence=0
   for L in range(-100,101):
    v=num(L)
    if v%C:continue
    N=v//C
    w=L+(2*p-q)*N-2*p*r+q
    if w%p:continue
    k=w//p
    if N>=r+1 and 0<=k<=N-r and L!=0:direct+=1
   for L in range(-100,101):
    if L%(p*C) not in roots:continue
    N=num(L)//C;k=(L+(2*p-q)*N-2*p*r+q)//p
    if N>=r+1 and 0<=k<=N-r and L!=0:congruence+=1
   if direct!=congruence:raise RuntimeError(('period',p,q,r))
   records.append({'p':p,'q':q,'r':r,'C':C,'S':len(roots),'roots_mod_C':h1,'roots_mod_p':h2})
examples=[x for x in records if (x['p'],x['q']) in [(3,4),(1,2)]]
out={'parameter_defect_cases':len(records),'all_checks_pass':True,'examples':examples}
Path(__file__).with_name('replay_low_counts.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
