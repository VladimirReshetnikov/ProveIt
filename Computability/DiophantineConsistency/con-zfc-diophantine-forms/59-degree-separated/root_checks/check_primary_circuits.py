#!/usr/bin/env python3
"""Independent cross-family count/domain/liveness audit of the delivered data."""
from pathlib import Path
from collections import Counter
import json
ROOT=Path(__file__).resolve().parents[1]
CASES=[('nine_free_adjunct/generated/split_116_positive.json',9,473),('nine_free_adjunct/generated/split_116_natural.json',9,480),('positive13_adjunct/thirteen_positive_degree126.json',13,91),('sun/generated/sun10.json',10,533),('nine/generated/split_116_positive.json',9,476),('nine/generated/split_116_natural.json',9,480),('signed/generated/signed_coprime_compact_split_crt.json',13,518),('signed/generated/signed_coprime_split_crt.json',13,520),('positive/ordinary_merger_product.json',12,102),('positive/ordinary_merger_system.json',12,95),('positive/ordinary_merger_shifted_system.json',12,94),('positive/ordinary_merger_sos.json',12,103)]
def req(p,m):
 if not p:raise ValueError(m)
results=[]
for file,n,k in CASES:
 d=json.loads((ROOT/file).read_text())
 if 'nodes' in d:
  nodes=d['nodes'];var=[x['name'] for x in nodes if x['kind']=='variable'];req(len(var)==n==len(set(var)),file+' variables')
  ops=Counter(x['kind'] for x in nodes if x['kind'] in ['add','sub','mul']);req(sum(ops.values())==k,file+' counts')
  live=set()
  def visit(i):
   if i in live:return
   req(isinstance(i,int) and 0<=i<len(nodes),file+' operand');live.add(i);x=nodes[i]
   if x['kind'] in ['add','sub','mul']:
    req(x['left']<i and x['right']<i,file+' topological');visit(x['left']);visit(x['right'])
   else:req(x['kind'] in ['literal','fixed','variable'],file+' uncharged operation')
  visit(d['output']);req(len(live)==len(nodes),file+' dead node')
 else:
  req(len(d['witnesses'])==n,file+' witness count');src=d['source'];req(len(src)==k,file+' count')
  definitions={x[0]:x for x in src};req(len(definitions)==len(src),file+' duplicate names')
  known=set(d['witnesses'])|set(d['fixed_numerals']);ops=Counter()
  for name,op,a,b in src:
   req(op in ['+','-','*'],file+' invalid op');ops[op]+=1
   req(all(isinstance(t,int) or t in known for t in [a,b]),file+' forward/unknown operand');known.add(name)
  live=set()
  def visit_name(x):
   if isinstance(x,int) or x not in definitions or x in live:return
   live.add(x);_,_,a,b=definitions[x];visit_name(a);visit_name(b)
  out=d.get('output',d.get('comparisons'))
  if isinstance(out,str):visit_name(out)
  else:
   def walk(x):
    if isinstance(x,str):visit_name(x)
    elif isinstance(x,list):
     for t in x:walk(t)
    elif isinstance(x,dict):
     for t in x.values():walk(t)
   walk(out)
  req(len(live)==len(src),file+' unused gate')
 results.append({'file':file,'variables':n,'operations':k,'counts':dict(ops),'all_gates_live':True})
out={'status':'PASS','circuits':results,'scope':'Independent finite gate/domain/liveness audit; degrees and mathematical equivalences have separate certificates.'}
Path(__file__).with_suffix('.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
