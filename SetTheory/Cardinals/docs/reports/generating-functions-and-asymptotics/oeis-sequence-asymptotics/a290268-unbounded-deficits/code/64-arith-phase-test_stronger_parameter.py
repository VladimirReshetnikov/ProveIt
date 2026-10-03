"""Counterexample search for a stronger, as-yet unproved structural lemma."""
from pathlib import Path
import json
checks=0;hits=[]
for d in range(1,13):
 for h in range(2*d,4*d+1):
  for q in range(121):
   r=h+q+1;c=h-q
   a=[1]+[0]*d
   for j in range(r):a=[(h-j)*a[i]+(a[i-1] if i else 0) for i in range(d+1)]
   b=[c*a[i]+(2*a[i-1] if i else 0) for i in range(d+1)]
   for k in range(1,41):
    checks+=1;forced=q==h and (k+d)%2==0
    if (b[d]==0)!=forced:
     hits.append({'d':d,'evaluation':h,'q':q,'k':k,'value':b[d],'forced':forced});print('HIT',hits[-1],flush=True)
     if len(hits)>=10:raise SystemExit
    z=[c*b[i]+(2*b[i-1] if i else 0)+k*(k+r)*a[i] for i in range(d+1)];a,b=b,z
print('PASS NO COUNTEREXAMPLE',checks,flush=True)
Path(__file__).with_name('stronger_parameter_scan.json').write_text(json.dumps({'checks':checks,'d_max':12,'evaluation_range':'2d..4d','q_max':120,'k_range':[1,40],'unexpected':hits},indent=2))
