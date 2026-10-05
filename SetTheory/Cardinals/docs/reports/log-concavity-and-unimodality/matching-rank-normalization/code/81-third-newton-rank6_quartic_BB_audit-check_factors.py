"""Exact positivity of BB R determinant factors on four pair-basis cones."""
from pathlib import Path
from itertools import product
import sympy as s
import json,hashlib,time
ROOT=Path(__file__).resolve().parent.parent/'rank6_quartic_truncation';OUT=Path(__file__).resolve().parent
a,b,c,p=s.symbols('a b c p');A,B,C=s.symbols('A B C');loc=dict(zip(('a','b','c','p'),(a,b,c,p)))
pop=a*b+a*c+b*c+c*(c-1)/2
bases=((1,1,0),(1,0,1),(0,1,1),(0,0,2))
records=[];start=time.time()
for path in sorted(ROOT.glob('BB_R_*_*.json')):
 data=json.loads(path.read_text());det=s.sympify(data['determinant'],locals=loc)
 const,factors=det.as_coeff_mul()
 if const<=0:raise RuntimeError(('negative scalar',path))
 rows=[]
 for factor in factors:
  base,power=factor.as_base_exp()
  if not power.is_Integer or power<=0:raise RuntimeError('nonpolynomial factor')
  expr=s.expand(base.subs(p,pop))
  for cone in bases:
   poly=s.Poly(s.expand(expr.subs({a:A+cone[0],b:B+cone[1],c:C+cone[2]},simultaneous=True)),A,B,C)
   if poly.is_zero or any(x<0 for x in poly.coeffs()):
    bad=[(e,str(x)) for e,x in poly.terms() if x<0]
    raise RuntimeError(('factor positivity fails',data['pair'],str(base),cone,bad[:8]))
   text=json.dumps([[list(e),str(x)] for e,x in sorted(poly.terms())],separators=(',',':'))
   rows.append({'factor':str(base),'power':int(power),'cone':cone,'terms':len(poly.terms()),'minimum':str(min(poly.coeffs())),'sha256':hashlib.sha256(text.encode()).hexdigest()})
 records.append({'pair':data['pair'],'all_pass':True,'source_sha256':hashlib.sha256(path.read_bytes()).hexdigest(),'factor_cone_checks':len(rows),'records':rows})
 print('PASS',data['pair'],len(rows),flush=True)
out={'all_available_pass':True,'profiles':len(records),'factor_cone_checks':sum(v['factor_cone_checks'] for v in records),'cone_bases':bases,'records':records,'seconds':time.time()-start}
(OUT/'factor_checks.json').write_text(json.dumps(out,indent=2)+'\n');print({k:v for k,v in out.items() if k!='records'})
