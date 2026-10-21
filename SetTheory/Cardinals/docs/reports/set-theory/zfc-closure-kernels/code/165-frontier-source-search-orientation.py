import json,hashlib
from pathlib import Path
import source_language as s,source_splice as sp
P=Path(__file__).resolve().parent
ss=json.loads((P/'sites215.json').read_text());root=s.tree(ss)
x=json.loads((P/'dag215.json').read_text());ns=[]
for n in x['nodes']:ns.append(tuple(n)if isinstance(n[0],str)else tuple(ns[i]for i in n))
out=[]
for ant in(0,1):
 for body in(0,1):
  rr=[list(z)for z in ss]
  ranges=[]
  if ant:ranges += [(505,531),(587,613)]
  if body:ranges += [(643,695),(723,775)]
  for lo,hi in ranges:
   for i in range(lo,hi):
    if rr[i][1]in('CI','CD')and rr[i][2]in(4,5):rr[i][2]=9-rr[i][2]
  t=s.tree(rr)
  for label,repl in [('R',None),('I',ns[76]),('Q',ns[77]),('E',(ns[77],ns[37]))]:
   new=t if repl is None else sp.apply_closed_splices(t,{(695,723):repl})
   metrics=s.metrics(new);path=P/f'orient_G{label}_{ant}{body}_{metrics["dag_nodes"]}.json';path.write_bytes(s.compact(s.sites(new)))
   out.append({'binder':label,'antecedents_swapped':bool(ant),'consequent_binder_swapped':bool(body),**metrics,'path':str(path)})
print(json.dumps(out,indent=2))
(P/'orientation_summary.json').write_text(json.dumps(out,indent=2)+'\n')

