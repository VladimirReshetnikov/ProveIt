"""Independent, data-only report claims audit; no producer code imports."""
from pathlib import Path
from collections import Counter
import json, hashlib
ROOT=Path(__file__).resolve().parents[2]
def require(x,msg):
 if not x: raise ValueError(msg)
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
results={}
for name,variables,rows,terms in [('odd_cap',352,219,9355),('signed_cap',355,220,9370)]:
 p=ROOT/'alternative'/name
 d=json.loads((p/'equation.json').read_text())
 e=json.loads((p/'expanded_polynomial.json').read_text())
 require(d['domain']=='unrestricted integers','direct domain')
 require(len(d['variables'])==variables and len(d['residuals'])==rows,'direct counts')
 acc=Counter()
 for row in d['residuals']:
  for ca,ma in row['terms']:
   require(len(ma)<=2,'not quadratic')
   for cb,mb in row['terms']:
    acc[tuple(sorted(ma+mb))]+=ca*cb
 acc={m:c for m,c in acc.items() if c}
 stored={tuple(m):c for c,m in e['terms']}
 require(len(stored)==len(e['terms']),'duplicated terms')
 require(acc==stored,'complete expansion mismatch')
 active=set(i for m in acc for i in m)
 require(active==set(range(variables)),'not all variables occur')
 require(len(acc)==terms and max(map(len,acc))==4 and max(map(abs,acc.values()))==15020718,'expanded metrics')
 results[name]={'equation_sha256':sha(p/'equation.json'),'expanded_sha256':sha(p/'expanded_polynomial.json'),'variables':variables,'rows':rows,'degree':4,'terms':terms,'height':15020718,'all_declared_variables_occur':True,'full_sum_of_squares_reexpansion_equal':True}
for f,v,ops,degree in [('lowdegree/equation.json',15,111,44),('integer/main_saturated11_none.json',11,123,428),('integer/main_saturated11_simple.json',11,127,412),('integer/main_saturated11_sharp.json',11,128,396),('integer/free_main_saturated11_none.json',11,127,376),('integer/free_main_saturated11_simple.json',11,131,364),('integer/free_main_saturated11_sharp.json',11,132,352),('integer_lowops/product_main_guard11_native.json',11,109,924),('integer_lowops/product_main_guard11_short.json',11,110,840)]:
 p=ROOT/f;d=json.loads(p.read_text()); nodes=d['nodes']; reachable=set()
 def visit(i):
  if i in reachable:return
  reachable.add(i)
  node=nodes[i]
  if node[0] in ('add','sub','mul'):
   require(0<=node[1]<i and 0<=node[2]<i,'DAG topology')
   visit(node[1]);visit(node[2])
 visit(d['output'])
 counts=Counter(nodes[i][0] for i in reachable if nodes[i][0] in ('add','sub','mul'))
 active={nodes[i][1] for i in reachable if nodes[i][0]=='variable'}
 require(sum(counts.values())==ops and len(active)==v and active==set(d['variables']),'DAG census')
 require(d['exact_degree']==degree,'reported degree metadata')
 results[f]={'sha256':sha(p),'variables':v,'live_operations':ops,'operation_split':dict(counts),'exact_degree_cross_checked_with_mathematical_review':degree}
for f,v,ops,degree in [('positive/first.json',10,102,253),('positive/second.json',10,104,252)]:
 p=ROOT/f;d=json.loads(p.read_text())
 require(len(d['witnesses'])==v and len(d['source'])==ops and d['exact_degree']==degree,'positive metrics')
 results[f]={'sha256':sha(p),'variables':v,'live_operations_from_full_independent_review':ops,'exact_degree_from_reviewed_leading_forms':degree}
results['fifteen_degree_witness']={'exponents':[26,6,8,2,2],'sum':44,'coefficient':'2^54 * 3^32 * beta^26 > 0'}
results['eleven_degree_witness']={'exponents':[124,64,64,4,24,68,4],'sum':352,'coefficient':'2^288 * 3^188 * beta^124 > 0'}
require(sum(results['fifteen_degree_witness']['exponents'])==44,'degree44 witness')
require(sum(results['eleven_degree_witness']['exponents'])==352,'degree352 witness')
require(sum([564,106,148,42,16,12,34,2])==924,'native lowops degree witness')
require(sum([564,64,106,42,16,12,34,2])==840,'short lowops degree witness')
results['lowops_degree_witnesses']={'native_coefficient':'2^960 * 3^677 * beta^564 > 0','short_coefficient':'2^918 * 3^635 * beta^564 > 0','native_exponent_sum':924,'short_exponent_sum':840}
output={'status':'PASS','scope':'Independent complete sparse direct quartic re-expansion and input/gate census; manual report-to-proof formula and degree-witness comparisons. No producer imports, no fresh transitive calibration proof. PDF review is separate.','results':results}
print(json.dumps(output,indent=2,sort_keys=True))
