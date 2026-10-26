#!/usr/bin/env python3
"""Select low-support prefixes of supplied elementary row operations."""
from pathlib import Path
import sys,json,copy
ROOT=Path(__file__).resolve().parent
sys.path.insert(0,str(ROOT/'inherited_radical'))
import reduce_radical as p

def run(n,source,reduced,limits):
 eq=json.loads((ROOT/source/'equation.json').read_text())
 ops=json.loads((ROOT/reduced/'row_certificate.json').read_text())['operations']
 rows=[p.norm(r['terms']) for r in eq['residuals']];exp=p.add(*(p.mul(r,r) for r in rows));best={}
 for k,op in enumerate([[0,1,0]]+ops):
  if k:
   i,j,a=op;old=rows[i];rows[i]=p.add(old,p.scale(rows[j],a));exp=p.add(exp,p.scale(p.mul(old,old),-1),p.mul(rows[i],rows[i]))
  h=max(map(abs,exp.values()))
  for limit in limits:
   score=(len(exp),h,k)
   if h<=limit and (limit not in best or score<best[limit][0]):best[limit]=(score,copy.deepcopy(rows),copy.deepcopy(exp))
 census={}
 for limit,(score,rr,exp) in best.items():
  target=copy.deepcopy(eq);target['variant']+=':integer_row_reduction';target['residuals']=[dict(r,terms=p.terms(q)) for r,q in zip(eq['residuals'],rr)]
  out=ROOT/f'pooled{n}_height{limit}';out.mkdir(exist_ok=True)
  cert={'schema':'integer_row_operations_v1','input_sha256':p.digest(eq),'operations':ops[:score[2]],'output_sha256':p.digest(target)}
  met=p.metric(target,True)
  for name,data in {'equation.json':target,'row_certificate.json':cert,'metrics.json':met,'expanded_polynomial.json':{'schema':'sparse_integer_polynomial_v1','variables':len(target['variables']),'terms':p.terms(exp)}}.items():(out/name).write_bytes(p.canonical(data))
  census[str(limit)]={'row_operations':score[2],**met}
 print(json.dumps({'dimension':n,'profiles':census},indent=2),flush=True)
 return census

if __name__=='__main__':
 params=[(220,'pooled220_sheared','pooled220_sheared_reduced',[2736,4408,6144,7968]),(219,'pooled219_affine','pooled219_reduced',[4408,4576,6144,7968]),(218,'pooled218_affine','pooled218_reduced',[4408,4576,6144,7968]),(217,'pooled223_radical','pooled217_reduced',[5184,6144,7968])]
 result={str(n):run(n,source,reduced,limits) for n,source,reduced,limits in params}
 (ROOT/'POOLED_PREFIX_CENSUS.json').write_text(json.dumps(result,sort_keys=True,indent=2)+'\n')
