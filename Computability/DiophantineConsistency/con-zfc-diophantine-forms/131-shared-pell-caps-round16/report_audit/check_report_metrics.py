#!/usr/bin/env python3
"""Independent complete SOS expansion for every reported selected quartic."""
from pathlib import Path
from collections import defaultdict
import json,hashlib,sys
R=Path(sys.argv[1]).resolve() if len(sys.argv)>1 else Path(__file__).resolve().parents[1]
choices=[('architecture/unified_cap_h12/natural','nonnegative integers',(249,4,186,27078,85178741)),('architecture/unified_cap_sparse_h12/natural','nonnegative integers',(278,4,215,5524,83852788)),('direct/integer324','unrestricted integers',(324,4,208,5808,128446)),('direct/integer338','unrestricted integers',(338,4,222,4493,128446))]
rows=[]
for sub,domain,expected in choices:
 p=R/sub;e=json.loads((p/'equation.json').read_text());x=json.loads((p/'expanded_polynomial.json').read_text());out=defaultdict(int)
 if e['domain']!=domain or x['domain']!=domain or x['variables']!=len(e['variables']):raise ValueError('domain/variables '+sub)
 for r in e['residuals']:
  terms=r['terms']
  for i,(a,m) in enumerate(terms):
   if type(a)!=int or len(m)>2 or any(type(j)!=int or j<0 or j>=len(e['variables']) for j in m):raise ValueError('residual syntax')
   for j in range(i,len(terms)):
    b,n=terms[j];out[tuple(sorted(m+n))]+=a*b*(1 if i==j else 2)
 out={m:c for m,c in out.items() if c}
 literal={tuple(m):c for c,m in x['terms']}
 if len(literal)!=len(x['terms']) or out!=literal:raise ValueError('full coefficient mismatch '+sub)
 got=(len(e['variables']),max(map(len,out)),len(e['residuals']),len(out),max(map(abs,out.values())))
 if got!=expected:raise ValueError(str((sub,got,expected)))
 rows.append({'endpoint':sub,'domain':domain,'variables':got[0],'degree':got[1],'rows':got[2],'monomials':got[3],'height':got[4],'full_SOS_expansion_exact':True,'equation_sha256':hashlib.sha256((p/'equation.json').read_bytes()).hexdigest()})
print(json.dumps({'status':'PASS','scope':'All selected quartic metrics and every expanded coefficient independently recomputed, without importing any producer or checker.','endpoints':rows},indent=2))
