import json
from pathlib import Path
from fractions import Fraction as F
import sympy as s
D=Path(__file__).parent;templates=json.loads((D/'templates.json').read_text())['templates'];certs=json.loads((D/'gap2_certificates.json').read_text());R={}
for r in templates:
 if r['gamma_id']in R:
  prior=R[r['gamma_id']];assert prior['gamma']==r['gamma'] and prior['gap2']==r['gap2']
 else:R[r['gamma_id']]=r
assert len(certs)==len(R) and {r['gamma_id']for r in certs}==set(R)
def plus(a,b):return tuple(x+y for x,y in zip(a,b))
counts={'unique_gamma':len(R),'binomial_positive':0,'face_templates':0,'verified_faces':0}
for record in certs:
 gid=record['gamma_id'];r=R[gid];xs=s.symbols(' '.join('n'+str(t)for t in r['types']),seq=True)
 def mono(poly):return s.expand(sum(v*s.prod(s.prod(x-j for j in range(k))/s.factorial(k)for x,k in zip(xs,q))for q,v in poly))
 p=mono(r['gap2']);g=[mono(g)for g in r['gamma']];assert s.expand(p-(g[2]**2-3*g[1]*g[3]))==0
 if record['kind']=='binomial_positive':
  assert all(v>=0 for q,v in r['gap2']);counts['binomial_positive']+=1;continue
 assert record['kind']=='faces' and not record['failures'];counts['face_templates']+=1
 assert len(record['faces'])==1<<len(xs) and {f['mask']for f in record['faces']}==set(range(1<<len(xs)))
 for face in record['faces']:
  active=[x for j,x in enumerate(xs)if face['mask']>>j&1];q=s.expand(p.subs({x:x+1 if x in active else 0 for x in xs},simultaneous=True));co={e:F(v)for e,v in s.Poly(q,*active).terms()}if active else{():F(q)};total={}
  for weight,poly,meta in face['terms']:
   weight=F(weight);assert weight>=0;poly={tuple(e):F(v)for e,v in poly}
   assert all(len(e)==len(active)and all(i>=0 for i in e)for e in poly)
   if meta is not None:
    m,z=meta;m=tuple(m);z=[(tuple(e),F(v))for e,v in z];square={}
    assert len(m)==len(active)and all(i>=0 for i in m)
    for a,u in z:
     assert len(a)==len(active)and all(i>=0 for i in a)
     for b,v in z:
      e=plus(m,plus(a,b));square[e]=square.get(e,F(0))+u*v
    square={e:v for e,v in square.items()if v};assert square==poly
   elif len(poly)==1:assert next(iter(poly.values()))>=0
   else:
    assert len(poly)==3
    neg=[(e,v)for e,v in poly.items()if v<0];pos=[(e,v)for e,v in poly.items()if v>0]
    assert len(neg)==1 and len(pos)==2
    (a,u),(b,v)=pos;(c,w),=neg
    assert all(i+j==2*k for i,j,k in zip(a,b,c)) and w*w==4*u*v
   for e,v in poly.items():total[e]=total.get(e,F(0))+weight*v
  total={e:v for e,v in total.items()if v};co={e:v for e,v in co.items()if v};assert co==total,(gid,face['mask'])
  counts['verified_faces']+=1
print('ALL EXACT CERTIFICATES VERIFIED',counts)
(D/'gap2_verification.json').write_text(json.dumps(counts,indent=2)+'\n')
