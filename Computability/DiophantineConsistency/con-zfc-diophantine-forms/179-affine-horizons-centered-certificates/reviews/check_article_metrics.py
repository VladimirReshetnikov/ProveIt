#!/usr/bin/env python3
"""Independent article metric recollection; imports no producer/checker."""
from pathlib import Path
from collections import Counter
import hashlib,json,sys
R=Path(__file__).resolve().parents[1]
def need(ok,msg):
 if not ok:raise ValueError(msg)
def entry(p):return {'path':str(p.relative_to(R)), 'sha256':hashlib.sha256(p.read_bytes()).hexdigest()}
out=[]
for rel,want in [
 ('integer/integer215_sparse',(215,152,14578,16866,4)),
 ('integer/integer215',(215,152,34700,4512,4)),
 ('natural/natural202',(202,154,9353,1854167,4)),
 ('natural/natural202_lowheight',(202,154,16927,416488,4)),
 ('natural/natural203',(203,155,6524,1979888,4)),
 ('natural/natural204',(204,156,6503,1981520,4)),
 ('natural/natural200_degree8',(200,152,10392,13654244,8))]:
 p=R/rel/'equation.json';d=json.loads(p.read_text());s=Counter();live=set()
 for row in d['residuals']:
  for c,m in row['terms']:
   live.update(m)
   for e,n in row['terms']:s[tuple(sorted(m+n))]+=c*e
 s={m:c for m,c in s.items() if c}
 got=(len(d['variables']),len(d['residuals']),len(s),max(map(abs,s.values())),max(map(len,s)))
 need(got==want,rel+' metrics');need(live==set(range(got[0])),rel+' variable liveness')
 x=entry(p);x.update(dict(zip(['variables','rows','terms','height','degree'],got)));x['all_variables_live']=True;x['max_residual_coefficient']=max(abs(c) for r in d['residuals'] for c,m in r['terms']);out.append(x)
for sub in ['', 'start_marker4177/', 'late172/']:
 specs=[('equation_bV.json',88),('equation_plus1_bV.json',87)] if sub!='late172/' else [('centerA_radix67.json',90),('centerA_start4177.json',90),('centerAp1_radix67.json',89),('centerAp1_start4177.json',89)]
 for filename,opcount in specs:
  p=R/'positive'/sub/filename;d=json.loads(p.read_text());defs={r[0]:r for r in d['source']};live=set();available=set(d['witnesses'])|set(d['fixed_numerals'])
  need(len(defs)==len(d['source']),'duplicate positive gates')
  for name,op,a,b in d['source']:
   need(name not in available and op in ['+','-','*'],'positive topology')
   need(all(type(x)==int or x in available for x in [a,b]),'positive undefined input');available.add(name)
  def walk(x):
   if type(x)==int or x in live:return
   live.add(x)
   if x in defs:
    for a in defs[x][2:]:walk(a)
  walk(d['output']);c=Counter(r[1] for r in d['source'] if r[0] in live)
  need(live==available,'positive graph liveness');need(sum(c.values())==opcount==d['operations'],'positive operation count');need(len(d['witnesses'])==10,'positive variable count')
  x=entry(p);x.update(variables=10,operations=opcount,counts=dict(c),all_gates_inputs_and_ports_live=True);out.append(x)
for degree,want in [(85,110),(87,108)]:
 p=R/f'roots/integer14_degree{degree}.json';d=json.loads(p.read_text());ns=d['nodes'];live=set()
 for i,node in enumerate(ns):
  if node[0] in ['mul','add','sub']:need(all(type(k)==int and 0<=k<i for k in node[1:]),'root topology')
 def walk(k):
  if k in live:return
  live.add(k)
  if ns[k][0] in ['mul','add','sub']:
   for n in ns[k][1:]:walk(n)
 walk(d['output']);c=Counter(ns[k][0] for k in live if ns[k][0] in ['mul','add','sub'])
 need(len(live)==len(ns),'root liveness');need(sum(c.values())==want==d['operations'],'root operations');need(len(d['variables'])==14,'root variable count')
 x=entry(p);x.update(variables=14,operations=want,counts=dict(c),all_nodes_live=True);out.append(x)
result={'status':'PASS','optimized':bool(sys.flags.optimize),'scope':'Full direct SOS recollection and compact DAG topology, input/gate liveness and operation recount. Compact exact-degree proofs are separately reviewed. No producer/checker imported.','endpoints':out}
print(json.dumps(result,indent=2))
