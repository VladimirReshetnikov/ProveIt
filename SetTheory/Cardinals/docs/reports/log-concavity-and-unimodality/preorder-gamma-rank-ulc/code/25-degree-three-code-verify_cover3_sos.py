import json,itertools
from fractions import Fraction as F
from pathlib import Path
import sympy as s
D=Path(__file__).parent;R=json.loads((D/'cover3_seventeen_templates.json').read_text())
for path in sorted(D.glob('cover3_sos_*.json')):
 data=json.loads(path.read_text());r=R[data['id']];xs=s.symbols(' '.join('n'+str(t)for t in r['types']),seq=True);p=s.sympify(r['gap_monomial'])
 for face in data['certified_faces']:
  active=[x for j,x in enumerate(xs)if face['mask']>>j&1];q=s.expand(p.subs({x:x+1 if x in active else 0 for x in xs},simultaneous=True));total=0
  for weight,poly in face['terms']:
   weight=F(weight);assert weight>=0
   poly={tuple(e):F(v)for e,v in poly}
   if len(poly)==1:assert next(iter(poly.values()))>=0
   else:
    assert len(poly)==3
    neg=[(e,v)for e,v in poly.items()if v<0];pos=[(e,v)for e,v in poly.items()if v>0]
    assert len(neg)==1 and len(pos)==2
    (a,u),(b,v)=pos;(c,w),=neg
    assert all(i+j==2*k for i,j,k in zip(a,b,c)) and w*w==4*u*v
   total+=s.Rational(weight.numerator,weight.denominator)*sum(s.Rational(v.numerator,v.denominator)*s.prod(x**k for x,k in zip(active,e))for e,v in poly.items())
  assert s.expand(q-total)==0,(data['id'],face['mask'])
 print('verified',data['id'],len(data['certified_faces']),'faces; missing',data['failed_masks'])
