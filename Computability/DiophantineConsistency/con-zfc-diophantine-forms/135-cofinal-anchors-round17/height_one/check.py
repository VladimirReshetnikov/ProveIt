#!/usr/bin/env python3
"""Independent exact checker for incidence-local height-one quartics.

Does not import contract.py or the producer. Expands vertex divergences and
alias/unit differences as a literal half-sum of squares. Normalization checks
reuse the independently authored incoming verifier, not the incoming producer.
Every test raises explicitly and remains active with python -O.
"""
import argparse, hashlib, json, sys
from collections import Counter, defaultdict
from copy import deepcopy
from pathlib import Path
HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE/'vendor'))
from verify_graph import normalization_check, add, multiply, sparse, require

def verify(source, artifact, cert, digest):
 require(cert['source_sha256']==digest,'Source hash')
 require(artifact['schema']=='incidence-local-height-one-quartic-v1','Artifact schema')
 require(cert['schema']=='incidence-local-height-one-certificate-v1','Certificate schema')
 require(source['domain']=='unrestricted integers' and artifact['domain']=='unrestricted integers','Integer domains')
 norm=cert['normalization']; normalization_check(source,norm)
 variables=artifact['variables']; n=len(variables); ln=len(norm['variables'])
 groups=defaultdict(set); flows=set(); ordinary_dummies=defaultdict(set); unit_dummies=set()
 for i,d in enumerate(variables):
  kind=d['kind']
  if kind in ('alias','equality_dummy'):
   v=d['normalized_variable']; require(v is None or type(v) is int and 0<=v<ln,'Logical index')
   require(d=={'kind':kind,'normalized_variable':v},'Exact alias metadata')
   if kind=='alias': groups[v].add(i)
   else:
    require(v is not None,'Ordinary dummy is not a unit'); ordinary_dummies[v].add(i)
  elif kind=='unit_dummy':
   require(d=={'kind':'unit_dummy'},'Unit dummy metadata'); unit_dummies.add(i)
  elif kind=='flow': flows.add(i)
  else: raise ValueError('Unknown coordinate kind')
 require(set(groups)=={None}|set(range(ln)),'Complete logical groups')
 products=cert['products']; flat=[(r,j,c,mon) for r,row in enumerate(norm['rows']) for j,(c,mon) in enumerate(row['terms'])]
 require(len(products)==len(flat),'Occurrence count'); used_aliases=set()
 for p,(r,j,c,mon) in zip(products,flat):
  require(p['row']==r and p['occurrence']==j and p['sign']==c,'Occurrence metadata')
  a,b=p['logical_factors']
  require(sorted(v for v in [a,b] if v is not None)==sorted(mon),'Logical source factors')
  require((len(mon)==2)==(b is not None) and (len(mon)>0)==(a is not None),'Homogenization')
  ids=p['factors']; require(len(ids)==2,'Quadratic product')
  for i,v in zip(ids,[a,b]):
   require(type(i) is int and 0<=i<n and i in groups[v],'Alias logical membership'); used_aliases.add(i)
 require(used_aliases==set.union(*groups.values()),'Unused factor alias')
 cycles=cert['equality_cycles']; require(len(cycles)==ln,'Cycle count'); seen=set(); covered=set()
 for cy in cycles:
  v=cy['normalized_variable']; ids=cy['aliases']
  require(type(v) is int and 0<=v<ln and v not in seen,'Cycle logical value'); seen.add(v)
  require(len(ids)==len(set(ids)) and not covered.intersection(ids),'Cycle disjointness')
  require(set(ids)==groups[v]|ordinary_dummies[v],'Cycle coverage')
  mode=cy.get('mode','cycle'); require(mode in ('cycle','quartic_pair'),'Equality mode')
  if mode=='quartic_pair': require(len(ids)==2 and len(ordinary_dummies[v])==0,'Quartic pair membership')
  else:
   require(len(ordinary_dummies[v])==(1 if len(groups[v])==2 else 0),'Exact dummy count')
   require(len(ids)==1 or len(ids)>=3,'No two-cycle')
  covered.update(ids)
 units=cert['unit_path']; require(len(units)>=2 and len(units)==len(set(units)),'Unit path')
 require(set(units)==groups[None]|unit_dummies and len(unit_dummies)==max(0,2-len(groups[None])),'Unit coverage')
 require(not covered.intersection(units) and not (covered|set(units)).intersection(flows),'Namespaces')
 require(covered|set(units)|flows==set(range(n)),'Variable coverage')
 vertices=cert['vertices']; edges=cert['edges']; blocks=cert['row_blocks']; hubs=cert['hub_vertices']
 require(len(blocks)==len(norm['rows']),'Row block count'); owner={}; components=[hubs]+blocks
 for k,block in enumerate(components):
  require(len(block)>0 and len(block)==len(set(block)),'Nonempty distinct block')
  for j,v in enumerate(block):
   require(type(v) is int and 0<=v<len(vertices) and v not in owner,'Vertex partition'); owner[v]=k
   expected={'kind':'hub','index':j} if k==0 else {'kind':'row','row':k-1,'part':j}
   require(vertices[v]==expected,'Vertex metadata')
 require(set(owner)==set(range(len(vertices))),'All vertices owned')
 incident=[{} for _ in vertices]; adjacent=[[] for _ in vertices]; graph_pairs=set(); prod_ids=set(); flow_ids=set()
 for ei,e in enumerate(edges):
  t,h=e['tail'],e['head']; require(t in owner and h in owner and t!=h,'Distinct edge endpoints')
  pair=tuple(sorted([t,h])); require(pair not in graph_pairs,'No parallel edges'); graph_pairs.add(pair)
  c,mon=e['coefficient'],e['monomial']
  if e['kind']=='prescribed':
   pi=e['product']; require(type(pi) is int and 0<=pi<len(products) and pi not in prod_ids,'Prescribed occurrence'); prod_ids.add(pi)
   p=products[pi]; require(c==p['sign'] and mon==p['factors'],'Prescribed polynomial')
   require(owner[t]==p['row']+1 and owner[h]==0,'Prescribed row orientation')
  else:
   require(e['kind']=='free' and c==1 and len(mon)==1,'Free edge form'); v=mon[0]
   require(v in flows and v not in flow_ids,'Distinct flow variable'); flow_ids.add(v)
   k=owner[t]; require(k==owner[h],'Internal tree edge')
   expected={'kind':'flow','component':'hub','edge':ei} if k==0 else {'kind':'flow','component':'row','row':k-1,'edge':ei}
   require(variables[v]==expected,'Flow binding'); adjacent[t].append(h); adjacent[h].append(t)
  add(incident[t],{tuple(sorted(mon)):c}); add(incident[h],{tuple(sorted(mon)):-c})
 require(prod_ids==set(range(len(products))) and flow_ids==flows,'Edge coverage')
 for block in components:
  reached=set(); todo=[block[0]]
  while todo:
   v=todo.pop()
   if v in reached: continue
   reached.add(v); todo+=adjacent[v]
  require(reached==set(block),'Connected internal block')
  require(sum(len(adjacent[v]) for v in block)==2*(len(block)-1),'Acyclic internal block')
 twice={}
 for d in incident: add(twice,multiply(d,d))
 for cy in cycles:
  ids=cy['aliases']
  if cy.get('mode','cycle')=='quartic_pair':
   a,b=ids
   for d in [{(a,a):1,(b,b):-1},{(a,a):1,tuple(sorted((a,b))):-1},{tuple(sorted((a,b))):1,(b,b):-1}]: add(twice,multiply(d,d))
   continue
  if len(ids)==1: continue
  for a,b in zip(ids,ids[1:]+ids[:1]):
   d={(a,):1,(b,):-1}; add(twice,multiply(d,d))
 differences=[{(units[0],):1,():-1},{(units[-1],):1,():-1}]
 differences += [{(a,):1,(b,):-1} for a,b in zip(units,units[1:])]
 for d in differences: add(twice,multiply(d,d))
 require(all(c%2==0 for c in twice.values()),'Integral half-energy')
 expected={m:c//2 for m,c in twice.items()}; terms=artifact['terms']
 require(all(m==sorted(m) for c,m in terms),'Sorted indices')
 require(len({tuple(m) for c,m in terms})==len(terms),'Collected monomials')
 require(terms==sorted(terms,key=lambda t:(len(t[1]),t[1])),'Canonical term order')
 actual=sparse(terms,n); require(actual==expected,'Exact half-sum-of-squares identity')
 require(set(actual.values())<={-1,1} and actual.get(())==1,'Height one and constant one')
 require({v for m in actual for v in m}==set(range(n)),'All variables occur')
 metrics={'variables':n,'degree':max(map(len,actual)),'monomials':len(actual),'coefficient_height':max(map(abs,actual.values())),
 'individual_degree':max(max(Counter(m).values()) for m in actual if m),'constant':actual[()],
 'source_variables':len(source['variables']),'source_rows':len(source['residuals']),
 'normalized_variables':ln,'normalized_rows':len(norm['rows']),'occurrences':len(products),'flow_variables':len(flows),
 'equality_dummies':sum(map(len,ordinary_dummies.values())),'unit_coordinates':len(units),
 'alias_coordinates':sum(map(len,groups.values())),'hubs':len(hubs),
 'positive_coefficients':sum(c==1 for c in actual.values()),'negative_coefficients':sum(c==-1 for c in actual.values())}
 if 'quartic_pair_classes' in artifact['metrics']: metrics['quartic_pair_classes']=sum(cy.get('mode')=='quartic_pair' for cy in cycles)
 require(metrics==artifact['metrics'],'Exact metrics'); require(metrics['degree']==4,'Quartic')
 return metrics

def eval_terms(terms,values):
 ans=0
 for c,mon in terms:
  z=c
  for v in mon: z*=values[v]
  ans+=z
 return ans

def lift(source, artifact,cert,x):
 """Canonical integral source-to-final map, defined even off the zero set."""
 norm=cert['normalization']; y=list(x)
 for d in norm['variables'][len(x):]:
  if d['kind']=='constant': y.append(d['value'])
  else: y.append(d['coefficient']*x[d['variable']])
 values=[]
 for d in artifact['variables']:
  if d['kind']=='flow': values.append(0)
  elif d['kind']=='unit_dummy' or d.get('normalized_variable') is None: values.append(1)
  else: values.append(y[d['normalized_variable']])
 ext=[0]*len(cert['vertices']); adjacent=[[] for _ in ext]
 for e in cert['edges']:
  t,h=e['tail'],e['head']
  if e['kind']=='prescribed':
   z=e['coefficient']
   for v in e['monomial']: z*=values[v]
   ext[t]+=z; ext[h]-=z
  else:
   adjacent[t].append((h,e['monomial'][0],1)); adjacent[h].append((t,e['monomial'][0],-1))
 for block in [cert['hub_vertices']]+cert['row_blocks']:
  root=block[0]; parent={root:None}; order=[root]
  for v in order:
   for w,i,sgn in adjacent[v]:
    if w not in parent: parent[w]=(v,i,-sgn); order.append(w)
  for v in reversed(order[1:]):
   p,i,sgn=parent[v]; values[i]=-sgn*ext[v]; ext[p]+=ext[v]; ext[v]=0
 return values,ext

def finite_checks(source,artifact,cert):
 # This verifies the off-zero identity exactly at deliberately non-solutions.
 # The accompanying theorem, not these samples, supplies universal correctness.
 tests=[]; n=len(source['variables'])
 for seed in range(5):
  x=[((i*17+seed*13)%7)-3 for i in range(n)]; z,remaining=lift(source,artifact,cert,x)
  rows=[eval_terms(r['terms'],x) for r in source['residuals']]
  expected=(sum(r*r for r in rows)+sum(rows)**2)//2
  require(eval_terms(artifact['terms'],z)==expected,'Off-zero lift identity sample')
  # Inverse map is literally a representative from each original alias class.
  for cy in cert['equality_cycles']:
   if cy['normalized_variable']<n: require(z[cy['aliases'][0]]==x[cy['normalized_variable']],'Lift inverse sample')
  tests.append(seed)
 return tests

def mutations(source,artifact,cert,digest):
 rejected=[]
 changes=[('coefficient',lambda a,c:a['terms'][0].__setitem__(0,-a['terms'][0][0])),
 ('source_hash',lambda a,c:c.__setitem__('source_sha256','0'*64)),
 ('logical_factor',lambda a,c:c['products'][0]['logical_factors'].__setitem__(0,None)),
 ('source_row',lambda a,c:c['normalization']['rows'].pop()),
 ('missing_edge',lambda a,c:c['edges'].pop()),
 ('missing_alias',lambda a,c:c['equality_cycles'][0]['aliases'].pop()),
 ('unit_endpoint',lambda a,c:c['unit_path'].__setitem__(-1,c['unit_path'][0])),
 ('metric',lambda a,c:a['metrics'].__setitem__('variables',a['metrics']['variables']-1))]
 for name,change in changes:
  a,c=deepcopy(artifact),deepcopy(cert); change(a,c)
  try: verify(source,a,c,digest)
  except (ValueError,TypeError,KeyError,IndexError): rejected.append(name)
  else: raise ValueError('Mutation accepted: '+name)
 return rejected

def main():
 p=argparse.ArgumentParser(); p.add_argument('--source',required=True,type=Path); p.add_argument('--artifact-dir',required=True,type=Path)
 p.add_argument('--output',type=Path); p.add_argument('--mutations',action='store_true'); a=p.parse_args()
 raw=a.source.read_bytes(); source=json.loads(raw); digest=hashlib.sha256(raw).hexdigest()
 artifact=json.loads((a.artifact_dir/'polynomial.json').read_text()); cert=json.loads((a.artifact_dir/'certificate.json').read_text())
 metrics=verify(source,artifact,cert,digest); samples=finite_checks(source,artifact,cert)
 rejected=mutations(source,artifact,cert,digest) if a.mutations else []
 receipt={'status':'pass','python_optimized':not __debug__,'source_sha256':digest,'metrics':metrics,'off_zero_samples':samples,'mutations_rejected':rejected,
 'checks':['topological monic normalization and exact source pullback','full alias and unit provenance','simple incidence graph and internal spanning trees',
 'independent literal half-sum-of-squares expansion','coefficient height one and constant one','complete variable/monomial/degree counts'],
 'scope':'Finite algebraic certificates. The accompanying ordinary proof supplies the unbounded zero-set equivalence; source consistency calibration is inherited, not re-proved here.'}
 text=json.dumps(receipt,sort_keys=True,indent=2)+'\n'
 if a.output: a.output.parent.mkdir(parents=True,exist_ok=True); a.output.write_text(text)
 print(text,end='')
if __name__=='__main__': main()
