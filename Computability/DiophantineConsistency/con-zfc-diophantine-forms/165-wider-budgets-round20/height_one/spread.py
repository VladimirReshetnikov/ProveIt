"""Eliminate equality dummies by polarizing same-logical square products.

An exact, deterministic postprocessor. Every accepted candidate is checked
against the entire final polynomial, not a local collision heuristic.
"""
import copy
from collections import Counter
from pathlib import Path
import sys
HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE/'upstream'))
import contract

def polynomial(c):
 p=contract.energy(c)
 def add(z,m):
  m=tuple(sorted(m));p[m]=p.get(m,0)+z
  if not p[m]:del p[m]
 for cy in c['equality_cycles']:
  ids=cy['aliases']
  if cy.get('mode','cycle')=='unit_product_cycle':
   a,b=ids;g=[cy['anchor'],cy['unit']];mons=[[a],[b],g]
   for m in mons:add(1,m+m)
   for m,n in zip(mons,mons[1:]+mons[:1]):add(-1,m+n)
  elif cy.get('mode','cycle')=='quartic_pair':
   a,b=ids
   for z,m in [(1,[a]*4),(1,[b]*4),(-1,[a,a,a,b]),(-1,[a,b,b,b])]:add(z,m)
  elif len(ids)>1:
   for a in ids:add(1,[a,a])
   for a,b in zip(ids,ids[1:]+ids[:1]):add(-1,[a,b])
 u=c['unit_path'];add(1,[])
 for a in u:add(1,[a,a])
 for a,b in zip(u,u[1:]):add(-1,[a,b])
 add(-1,[u[0]]);add(-1,[u[-1]])
 return p

def spread(artifact,certificate):
 a=copy.deepcopy(artifact);c=copy.deepcopy(certificate);removed=set();records=[]
 for cy in c['equality_cycles']:
  if cy.get('mode')!='cycle' or len(cy['aliases'])!=3:continue
  ids=[i for i in cy['aliases'] if a['variables'][i]['kind']!='equality_dummy']
  ds=[i for i in cy['aliases'] if a['variables'][i]['kind']=='equality_dummy']
  if len(ids)!=2 or len(ds)!=1:continue
  sq=[(i,p) for i,p in enumerate(c['products']) if p['factors'][0]==p['factors'][1] and p['factors'][0] in ids]
  if not sq:continue
  olds=[(i,p,p['factors'],next(e for e in c['edges'] if e.get('product')==i)) for i,p in sq]
  oldcycle=cy['aliases'];cy['aliases']=ids;cy['mode']='quartic_pair'
  for i,p,old,e in olds:p['factors']=ids[:];e['monomial']=ids[:]
  p=polynomial(c)
  if max(map(abs,p.values()))<=1:
   removed.update(ds);records.append({'normalized_variable':cy['normalized_variable'],'products':[i for i,p,old,e in olds],'old_factors':[old for i,p,old,e in olds],'new_factors':ids,'deleted_dummy':ds[0]})
  else:
   cy['aliases']=oldcycle;cy['mode']='cycle'
   for i,p,old,e in olds:p['factors']=old;e['monomial']=old
 rename={i:j for j,i in enumerate(i for i in range(len(a['variables'])) if i not in removed)}
 a['variables']=[v for i,v in enumerate(a['variables']) if i not in removed]
 for cy in c['equality_cycles']:cy['aliases']=[rename[i] for i in cy['aliases']]
 c['unit_path']=[rename[i] for i in c['unit_path']]
 for p in c['products']:p['factors']=[rename[i] for i in p['factors']]
 for e in c['edges']:e['monomial']=[rename[i] for i in e['monomial']]
 # root_map concerns the first contraction stage; explicitly retain pre-spread namespace.
 c['polarization']={'schema':'same-logical-square-polarization-v1','input_variables':len(artifact['variables']),'removed_dummies':len(removed),'records_pre_compaction':records,'retained_input_indices':list(rename)}
 p=polynomial(c)
 if set(p.values())!={-1,1}:raise ValueError('final exact height')
 if {i for m in p for i in m}!=set(range(len(a['variables']))):raise ValueError('final live variables')
 a['terms']=[[p[m],list(m)] for m in sorted(p,key=lambda m:(len(m),m))]
 a['metrics'].update({'variables':len(a['variables']),'monomials':len(p),'equality_dummies':sum(v['kind']=='equality_dummy' for v in a['variables']),'quartic_pair_classes':sum(cy['mode']=='quartic_pair' for cy in c['equality_cycles']),'positive_coefficients':sum(z>0 for z in p.values()),'negative_coefficients':sum(z<0 for z in p.values()),'polarized_products':sum(len(r['products']) for r in records),'removed_equality_dummies':len(removed)})
 return a,c
