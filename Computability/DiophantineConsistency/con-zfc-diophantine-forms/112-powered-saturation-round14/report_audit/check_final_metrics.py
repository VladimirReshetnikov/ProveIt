#!/usr/bin/env python3
"""Final-report reviewer: independently reconstruct every principal quartic coefficient."""
import collections, hashlib, json
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
RESULT=[]
for relative,expected in [
 ('direct/integer519_centered',(519,321,4,6253,411060)),
 ('direct/derived16_centered_shell',(517,310,4,6774,3904267)),
 ('architecture/derived16_cantor/natural',(349,268,4,12768,86915503)),
]:
 p=ROOT/relative
 d=json.loads((p/'equation.json').read_text()); e=json.loads((p/'expanded_polynomial.json').read_text())
 out=collections.defaultdict(int)
 for row in d['residuals']:
  terms=row['terms']
  if any(len(m)>2 for c,m in terms): raise ValueError('Nonquadratic residual')
  for c,m in terms:
   for b,n in terms: out[tuple(sorted(m+n))]+=c*b
 out={m:c for m,c in out.items() if c}
 delivered={tuple(m):c for c,m in e['terms']}
 if len(delivered)!=len(e['terms']): raise ValueError('Duplicate delivered monomial')
 if out!=delivered: raise ValueError('Expanded polynomial mismatch')
 metrics=(len(d['variables']),len(d['residuals']),max(map(len,out)),len(out),max(map(abs,out.values())))
 if metrics!=expected: raise ValueError((relative,metrics,expected))
 used=set(v for m in out for v in m)
 if used!=set(range(metrics[0])): raise ValueError('Inactive or invalid variable')
 if e['variables']!=len(d['variables']) or e['domain']!=d['domain']: raise ValueError('Variable/domain mismatch')
 RESULT.append({'path':relative,'domain':d['domain'],'variables':metrics[0], 'residuals':metrics[1], 'degree':metrics[2], 'monomials':metrics[3], 'height':metrics[4], 'coefficientwise_reconstruction':'PASS','all_variables_live':True,'sha256':{f:hashlib.sha256((p/f).read_bytes()).hexdigest() for f in ['equation.json','expanded_polynomial.json']}})
print(json.dumps({'status':'PASS','scope':'Literal algebra and metrics only; not semantic calibration.','endpoints':RESULT},indent=2))
