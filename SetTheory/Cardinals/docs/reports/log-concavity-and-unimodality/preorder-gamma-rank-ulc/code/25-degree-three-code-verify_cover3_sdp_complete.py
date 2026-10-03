import json
from pathlib import Path
from fractions import Fraction as F
import sympy as s
D=Path(__file__).parent;R=json.loads((D/'cover3_seventeen_templates.json').read_text())
def plus(a,b):return tuple(x+y for x,y in zip(a,b))
for idx in [4,7]:
 r=R[idx];xs=s.symbols(' '.join('n'+str(t)for t in r['types']),seq=True);p=s.sympify(r['gap_monomial']);old=json.loads((D/f'cover3_sos_{idx}.json').read_text());faces=json.loads((D/('cover3_sdp_7_complete.json' if idx==7 else 'cover3_sdp_4.json')).read_text());assert set(f['mask']for f in faces)==set(old['failed_masks'])
 for face in faces:
  active=[x for j,x in enumerate(xs)if face['mask']>>j&1];q=s.expand(p.subs({x:x+1 if x in active else 0 for x in xs},simultaneous=True));co={e:F(v)for e,v in s.Poly(q,*active).terms()};total={}
  for weight,poly,meta in face['terms']:
   weight=F(weight);assert weight>=0;poly={tuple(e):F(v)for e,v in poly}
   if meta is not None:
    m,z=meta;m=tuple(m);z=[(tuple(e),F(v))for e,v in z];square={}
    assert all(i>=0 for i in m)
    for a,u in z:
     assert all(i>=0 for i in a)
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
  total={e:v for e,v in total.items()if v};co={e:v for e,v in co.items()if v};assert co==total,(idx,face['mask'])
  print('EXACT VERIFIED',idx,face['mask'],flush=True)
 print('ALL MISSING FACES CERTIFIED',idx,len(faces),flush=True)
