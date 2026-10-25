"""Delete internal tree flows by exact height-checked vertex contractions.

This graph transformation is zero-set bijective over integers.  The output is
accepted only after the complete collected polynomial has coefficient height 1.
"""
import copy
from collections import Counter
from spread import polynomial

def quotient(c,e):
 d=copy.deepcopy(c);u,v=e['tail'],e['head'];w=e['monomial'][0]
 d['edges']=[f for f in d['edges'] if not (f['kind']=='free' and f['monomial']==[w])]
 for f in d['edges']:
  for k in ['tail','head']:
   if f[k]==v:f[k]=u
 return d

def compress(artifact,certificate,policy='all'):
 a=copy.deepcopy(artifact);c=copy.deepcopy(certificate);removed=set();dead=set();records=[]
 # Endpoint degrees are refreshed at the start of each sweep. Tie-breaks are
 # literal input indices, not randomized or environment-dependent.
 while True:
  added=0;inc=Counter(v for e in c['edges'] for v in [e['tail'],e['head']])
  opts=sorted((e for e in c['edges'] if e['kind']=='free'),key=lambda e:(inc[e['tail']]*inc[e['head']],e['monomial']))
  for e in opts:
   if e not in c['edges']:continue
   d=quotient(c,e);p=polynomial(d)
   if max(map(abs,p.values()))>1:continue
   if policy=='support_nonincrease' and len(p)>len(polynomial(c)):continue
   w=e['monomial'][0];u,v=e['tail'],e['head']
   c=d;removed.add(w);dead.add(v);added+=1
   records.append({'flow':w,'tail':u,'head':v,'monomials_after':len(p)})
  if not added:break
 keep=[i for i in range(len(a['variables'])) if i not in removed];ren={i:j for j,i in enumerate(keep)}
 vertices=[i for i in range(len(c['vertices'])) if i not in dead];vr={i:j for j,i in enumerate(vertices)}
 a['variables']=[v for i,v in enumerate(a['variables']) if i in ren]
 c['vertices']=[v for i,v in enumerate(c['vertices']) if i in vr]
 for e in c['edges']:
  e['monomial']=[ren[i] for i in e['monomial']];e['tail']=vr[e['tail']];e['head']=vr[e['head']]
 for p in c['products']:p['factors']=[ren[i] for i in p['factors']]
 for cy in c['equality_cycles']:
  cy['aliases']=[ren[i] for i in cy['aliases']]
  if cy.get('mode')=='unit_product_cycle':cy['anchor']=ren[cy['anchor']];cy['unit']=ren[cy['unit']]
 c['unit_path']=[ren[i] for i in c['unit_path']]
 c['hub_vertices']=[vr[i] for i in c['hub_vertices'] if i in vr]
 c['row_blocks']=[[vr[i] for i in b if i in vr] for b in c['row_blocks']]
 # Earlier contraction and polarization ledgers intentionally retain their
 # pre-flow namespaces; the new map explicitly composes those namespaces.
 c['flow_contraction']={'schema':'internal-tree-flow-contraction-v1','policy':policy,'input_variables':len(artifact['variables']),'input_vertices':len(certificate['vertices']),'records_pre_compaction':records,'retained_input_indices':keep,'retained_input_vertices':vertices}
 p=polynomial(c)
 if set(p.values())!={-1,1} or p.get(())!=1 or max(map(len,p))!=4:raise ValueError('quartic exact height and constant')
 if {i for m in p for i in m}!=set(range(len(a['variables']))):raise ValueError('live variables')
 a['terms']=[[p[m],list(m)] for m in sorted(p,key=lambda m:(len(m),m))]
 a['metrics'].update({'variables':len(a['variables']),'monomials':len(p),'flow_variables':sum(v['kind']=='flow' for v in a['variables']),'positive_coefficients':sum(z>0 for z in p.values()),'negative_coefficients':sum(z<0 for z in p.values()),'hubs':len(c['hub_vertices']),'removed_flow_variables':len(removed)})
 return a,c
