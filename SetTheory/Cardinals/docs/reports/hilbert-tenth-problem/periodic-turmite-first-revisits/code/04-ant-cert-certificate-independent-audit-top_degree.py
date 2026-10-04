#!/usr/bin/env python3
"""Exact top-residual identities from current data, no full coefficient expansion."""
import sys
sys.dont_write_bytecode=True
from pathlib import Path
import os,json
import sympy as s
R=Path(os.environ.get('ANT_CERTIFICATE_ROOT','/workspace/shared/complete-ant-certificate-recovered-20261004-v2')).resolve();H=Path(__file__).resolve().parent
d=json.loads((R/'data/pair_inline-dag.json').read_text());nodes={n[0]:n for n in d['nodes']};W=s.Symbol('History:W');v=576000;cache={'G':W**v}
def val(n):
 if type(n)is int:return s.Integer(n)
 if n in cache:return cache[n]
 if n not in nodes:return s.Symbol('Init:Recoder:'+n)
 _,op,a,b=nodes[n];a,b=val(a),val(b);cache[n]=a+b if op=='+' else a-b if op=='-' else a*b;return cache[n]
rows=[]
for idx,side in [(13,'L'),(127,'R')]:
 a,b=d['equations'][idx];actual=s.expand(val(a)-val(b));expected=2*(s.Symbol('Init:Recoder:'+side+'_e1_aMinus1')+1)*W**v-s.Symbol('Init:Recoder:'+side+'_e1_T')-W**(2*v)-1
 if s.expand(actual-expected)!=0:raise ValueError('changed top residual')
 poly=s.Poly(actual,*sorted(actual.free_symbols,key=str));degree=int(poly.total_degree())
 leading=sum(c*s.prod(x**p for x,p in zip(poly.gens,mon)) for mon,c in poly.terms() if sum(mon)==degree)
 if degree!=2*v or leading!=-W**(2*v):raise ValueError('top homogeneous part')
 rows.append({'pair_residual':idx,'initializer_residual':idx+3,'global_residual':idx+3+48,'actual_polynomial':str(actual),'exact_total_degree':degree,'highest_homogeneous_part':str(leading)})
r={'status':'PASS_FRESH_EXACT_TOP_RESIDUALS','rows':rows,'degree_variable':'independent positive witness History:W','final_leading_part':'2*History:W^2304000','final_degree':2304000,'other_residuals_bound_source':'fresh independent complete-stream receipt, maximum 1127949'}
(H/'degree-direct-receipt.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(r,indent=2))
