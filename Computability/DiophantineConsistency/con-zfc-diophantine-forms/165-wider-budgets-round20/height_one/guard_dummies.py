"""Replace an equality dummy by an existing alias times an anchored unit.

The replacement is selected deterministically by complete polynomial support,
then alias/unit indices.  Exact height checking is performed on every changed
coefficient and once again on the full collected result after compaction.
"""
import copy
from collections import Counter
from spread import polynomial

def guarded(artifact,certificate):
 a=copy.deepcopy(artifact);c=copy.deepcopy(certificate);p=polynomial(c);gone=set();records=[]
 for cy in c['equality_cycles']:
  if cy.get('mode','cycle')!='cycle':continue
  ids=[i for i in cy['aliases'] if a['variables'][i]['kind']!='equality_dummy'];ds=[i for i in cy['aliases'] if a['variables'][i]['kind']=='equality_dummy']
  if len(ids)!=2 or len(ds)!=1:continue
  d=ds[0];affected={m:z for m,z in p.items() if d in m};best=None
  for anchor in ids:
   for unit in c['unit_path']:
    delta=Counter()
    for m,z in affected.items():
     delta[m]-=z;new=tuple(sorted(j for i in m for j in ([anchor,unit] if i==d else [i])));delta[new]+=z
    if any(abs(p.get(m,0)+z)>1 for m,z in delta.items()):continue
    support=len(p)+sum((p.get(m,0)+z!=0)-(p.get(m,0)!=0) for m,z in delta.items())
    score=(support,anchor,unit)
    if best is None or score<best[0]:best=score,delta
  if best is None:continue
  (support,anchor,unit),delta=best
  for m,z in delta.items():
   v=p.get(m,0)+z
   if v:p[m]=v
   else:p.pop(m,None)
  cy.update({'aliases':ids,'mode':'unit_product_cycle','anchor':anchor,'unit':unit});gone.add(d)
  records.append({'normalized_variable':cy['normalized_variable'],'deleted_dummy':d,'anchor':anchor,'unit':unit,'monomials_after':support})
 keep=[i for i in range(len(a['variables'])) if i not in gone];ren={i:j for j,i in enumerate(keep)}
 a['variables']=[a['variables'][i] for i in keep]
 for cy in c['equality_cycles']:
  cy['aliases']=[ren[i] for i in cy['aliases']]
  if cy.get('mode')=='unit_product_cycle':cy['anchor']=ren[cy['anchor']];cy['unit']=ren[cy['unit']]
 c['unit_path']=[ren[i] for i in c['unit_path']]
 for q in c['products']:q['factors']=[ren[i] for i in q['factors']]
 for e in c['edges']:e['monomial']=[ren[i] for i in e['monomial']]
 c['unit_guard_substitution']={'schema':'anchored-unit-dummy-substitution-v1','input_variables':len(artifact['variables']),'retained_input_indices':keep,'records_pre_compaction':records}
 expected={tuple(ren[i] for i in m):z for m,z in p.items()};p=polynomial(c)
 if expected!=p:raise ValueError('guarded full polynomial substitution')
 if set(p.values())!={-1,1} or p.get(())!=1 or max(map(len,p))!=4:raise ValueError('guarded quartic height/constant')
 if {i for m in p for i in m}!=set(range(len(a['variables']))):raise ValueError('guarded live variables')
 a['terms']=[[p[m],list(m)] for m in sorted(p,key=lambda m:(len(m),m))]
 a['metrics'].update({'variables':len(a['variables']),'monomials':len(p),'equality_dummies':sum(v['kind']=='equality_dummy' for v in a['variables']),'positive_coefficients':sum(z>0 for z in p.values()),'negative_coefficients':sum(z<0 for z in p.values()),'unit_product_cycle_classes':sum(cy.get('mode')=='unit_product_cycle' for cy in c['equality_cycles']),'unit_guard_removed_dummies':len(gone)})
 return a,c
