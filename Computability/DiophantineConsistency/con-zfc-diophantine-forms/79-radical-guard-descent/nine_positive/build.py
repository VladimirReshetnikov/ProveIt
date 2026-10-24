#!/usr/bin/env python3
"""Build the direct-polynomial-part nine-positive equation, standard library.
Source/ratio prefix is copied as inert JSON from pinned source71. New tail is
specified by654literal integer monomials. Every binary arithmetic gate counts.
"""
from pathlib import Path
from collections import Counter,defaultdict
from functools import lru_cache
import json,itertools,hashlib
from circuit import DAG
ROOT=Path(__file__).resolve().parent

def build(order=(2,3,0,1),variant='horner'):
 old=json.loads((ROOT/'upstream/nine71.json').read_text());d=DAG();env=[]
 for node in old['nodes']:
  k=node['kind']
  if k=='literal':idx=d.const(node['value'])
  elif k=='variable':idx=d.var(node['name'])
  elif k=='fixed':idx=d.fixed(node['name'])
  else:idx=d.binary(k,env[node['left']],env[node['right']])
  env.append(idx)
 regs={k:env[v]for k,v in old['named_nodes'].items()}
 for k,v in regs.items():d.save(k,v)
 c,add,sub,mul,pw=d.const,d.plus,d.minus,d.times,d.power
 A,C=regs['A'],regs['C'];ii=d.var('i');jj=sub(d.var('j'),c(1))
 Z=d.save('Z',add(regs['B1'],mul(jj,C)))
 data=json.loads((ROOT/'data/radical.json').read_text());poly={tuple(e):int(v)for e,v in data['T_terms']}
 variables=(A,C,ii,Z)
 @lru_cache(None)
 def evaluate(items):
  poly=dict(items)
  if not poly:return c(0)
  if all(not any(e)for e in poly):return c(sum(poly.values()))
  # Pull common monomial, important for i/Z factors.
  common=tuple(min(e[j]for e in poly)for j in range(4))
  if any(common):
   rest={tuple(e[j]-common[j]for j in range(4)):v for e,v in poly.items()}
   out=evaluate(tuple(sorted(rest.items())))
   return mul(out,*(pw(variables[j],e)for j,e in enumerate(common)if e))
  if variant=='greedy':
   j=max(range(4),key=lambda j:(sum(e[j]>0 for e in poly),sum(e[j]for e in poly),j))
  else:j=next(j for j in order if any(e[j]for e in poly))
  groups=defaultdict(dict)
  for e,v in poly.items():
   ee=list(e);power=ee[j];ee[j]=0;groups[power][tuple(ee)]=v
  ex=max(groups);out=evaluate(tuple(sorted(groups.pop(ex).items())))
  for ne in sorted(groups,reverse=True):
   out=add(mul(out,pw(variables[j],ex-ne)),evaluate(tuple(sorted(groups[ne].items()))));ex=ne
  return mul(out,pw(variables[j],ex))
 Pstar=d.save('Pstar',evaluate(tuple(sorted(poly.items()))))
 V1=d.save('direct_V1',Pstar);scale=d.save('direct_scale',mul(c(65536),pw(C,7)))
 a1=d.save('direct_a1',mul(pw(scale,2),regs['a1']))
 Omega,E0,V0,a0=map(regs.get,['Omega','E0','V0','a0'])
 theta=d.save('direct_theta',sub(E0,mul(Omega,add(V0,V1))))
 inner=d.save('direct_inner',sub(pw(theta,2),mul(pw(Omega,2),add(a0,a1))))
 out=d.save('direct_F9',sub(pw(inner,2),mul(c(4),pw(Omega,4),a0,a1)))
 nodes,out,names=d.prune(out);counts=dict(Counter(n['kind']for n in nodes if n['kind']in('add','sub','mul')))
 result={k:v for k,v in old.items()if k not in ['schema','nodes','output','named_nodes','operation_counts','total_operations','exact_degree']}
 result.update(schema='direct-radical-majorant-nine-v1',nodes=nodes,output=out,named_nodes=names,operation_counts=counts,total_operations=sum(counts.values()),exact_degree=1158228,majorant_monomials=654,defect_monomials=3781,majorant_order=list(order),majorant_method=variant,source_baseline_sha256=hashlib.sha256((ROOT/'upstream/nine71.json').read_bytes()).hexdigest())
 return result

def main():
 scores=[];winner=None
 for order in itertools.permutations(range(4)):
  b=build(order)
  scores.append({'method':'horner','order':order,'operations':b['total_operations']})
  if winner is None or b['total_operations']<winner['total_operations']:winner=b
 b=build(variant='greedy');scores.append({'method':'greedy','order':[0,1,2,3],'operations':b['total_operations']})
 if b['total_operations']<winner['total_operations']:winner=b
 (ROOT/'equation9.json').write_text(json.dumps(winner,indent=2)+'\n')
 (ROOT/'certificates/horner_choices.json').write_text(json.dumps(scores,indent=2)+'\n')
 print(json.dumps({'operations':winner['total_operations'],'degree':winner['exact_degree'],'counts':winner['operation_counts'],'order':winner['majorant_order'],'method':winner['majorant_method']}))
if __name__=='__main__':main()
