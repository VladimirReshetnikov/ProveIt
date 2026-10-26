"""Height-checked unit homogenization of two-alias equality cycles.

Replace a two-alias penalty by C(f1,f2,f3), where each fi is either
one of its aliases or that alias times an already anchored unit. Both
aliases occur. Each candidate is checked against the full collected map.
The finite search deliberately includes a bare first form, tries both
alias orders, and is not claimed exhaustive over all possible penalties.
"""
import copy
from collections import Counter
from itertools import product
from spread import polynomial

def cycle(forms):
 p=Counter()
 for m in forms:p[tuple(sorted(m+m))]+=1
 for m,n in zip(forms,forms[1:]+forms[:1]):p[tuple(sorted(m+n))]-=1
 return {m:z for m,z in p.items() if z}

def old_penalty(cy):
 a,b=cy['aliases']
 if cy['mode']=='quartic_pair':return {(a,a,a,a):1,(b,b,b,b):1,tuple(sorted([a,a,a,b])):-1,tuple(sorted([a,b,b,b])):-1}
 return cycle([[a],[b],[cy['anchor'],cy['unit']]])

def homogenize(artifact,certificate):
 a=copy.deepcopy(artifact);c=copy.deepcopy(certificate);p=polynomial(c);records=[];opts=[[]]+[[u] for u in c['unit_path']]
 for cy in c['equality_cycles']:
  if cy.get('mode') not in ('quartic_pair','unit_product_cycle'):continue
  prev=old_penalty(cy);base=p.copy()
  for m,z in prev.items():
   v=base.get(m,0)-z
   if v:base[m]=v
   else:base.pop(m,None)
  best=None;ids=cy['aliases']
  for first,second in [ids,ids[::-1]]:
   for anchor in ids:
    for u,v in product(opts,repeat=2):
     forms=[[first],[second]+u,[anchor]+v]
     if len({tuple(sorted(f)) for f in forms})!=3:continue
     candidate=cycle(forms)
     if any(abs(base.get(m,0)+z)>1 for m,z in candidate.items()):continue
     support=len(base)+sum((base.get(m,0)+z!=0)-(base.get(m,0)!=0) for m,z in candidate.items())
     if support>=len(p):continue
     score=(support,tuple(map(tuple,forms)))
     if best is None or score<best[0]:best=score,forms,candidate
  if best is None:continue
  score,forms,candidate=best;before=copy.deepcopy(cy)
  cy.clear();cy.update({'normalized_variable':before['normalized_variable'],'aliases':ids,'mode':'anchored_cycle','forms':forms})
  p=base
  for m,z in candidate.items():
   v=p.get(m,0)+z
   if v:p[m]=v
   else:p.pop(m,None)
  records.append({'normalized_variable':cy['normalized_variable'],'old_relation':before,'new_forms':forms,'monomials_after':len(p)})
 c['anchored_homogenization']={'schema':'anchored-equality-cycle-homogenization-v1','records':records}
 if polynomial(c)!=p:raise ValueError('homogenized full coefficient reconstruction')
 if set(p.values())!={-1,1} or p.get(())!=1 or max(map(len,p))!=4:raise ValueError('homogenized quartic height and constant')
 if {i for m in p for i in m}!=set(range(len(a['variables']))):raise ValueError('homogenized live variables')
 a['terms']=[[p[m],list(m)] for m in sorted(p,key=lambda m:(len(m),m))]
 a['metrics'].update({'monomials':len(p),'positive_coefficients':sum(z>0 for z in p.values()),'negative_coefficients':sum(z<0 for z in p.values()),'anchored_cycle_classes':sum(cy.get('mode')=='anchored_cycle' for cy in c['equality_cycles']),'quartic_pair_classes':sum(cy.get('mode')=='quartic_pair' for cy in c['equality_cycles']),'unit_product_cycle_classes':sum(cy.get('mode')=='unit_product_cycle' for cy in c['equality_cycles'])})
 return a,c
