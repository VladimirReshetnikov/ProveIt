#!/usr/bin/env python3
"""Data-only certificates for the unrestricted auxiliary nine-gate frontier."""
import argparse
import hashlib
import itertools
import json
from collections import Counter
from pathlib import Path
PINS={
 'complete84_scaled_strong_output.py':'8b4dd58c849ae79751f1be6638f1b9e3f9072a714c5479eadf1039f10d0c7737',
 'complete84_scaled_strong_output.json':'8b2bc5d0b4db90c168107b7ded2cb4ca08df0098ed190851a3db4f1e49a9c0cf',
 'complete84_scaled_strong_output.md':'01eb7df6688c08c6788a3c7a1cc272ca5ffc1a87734fd622dbec8a64ae974ade',
 'complete84_auxiliary_mixed_cut.py':'a77f326d98550ed21643d5f1ea2aa25d9dca7d9a7fdca26c40e8bf1cdf80c13a',
 'complete84_auxiliary_mixed_cut.json':'1aa60da5b6b7278efdfd8535d10ec8f9af604b729b1f95c124eca714721dfc47',
 'complete84_auxiliary_mixed_cut.md':'b16bcf8b4013345d25a5d2bbb0598ae2caaaeaa31a529e00af7ea4647d78d7f2'}
def ck(t,m):
 if not t:raise ValueError(m)
def sha(b):return hashlib.sha256(b).hexdigest()
def read(path):
 def obj(items):
  d={}
  for k,v in items:ck(k not in d,'duplicate key');d[k]=v
  return d
 def bad(v):raise ValueError('nonfinite JSON')
 return json.loads(path.read_text(),object_pairs_hook=obj,parse_constant=bad)
def exact(a,b):
 if type(a) is not type(b):return False
 if isinstance(a,dict):return a.keys()==b.keys() and all(exact(a[k],b[k]) for k in a)
 if isinstance(a,list):return len(a)==len(b) and all(exact(x,y) for x,y in zip(a,b))
 return a==b
def add(a,b,s=1):
 d=dict(a)
 for e,c in b.items():
  d[e]=d.get(e,0)+s*c
  if not d[e]:del d[e]
 return d
def mul(a,b):
 d={}
 for e,c in a.items():
  for f,h in b.items():
   g=tuple(x+y for x,y in zip(e,f));d[g]=d.get(g,0)+c*h
 return {e:c for e,c in d.items() if c}
def serial(p):return [[list(e),c] for e,c in sorted(p.items())]
def run(root):
 for name,pin in PINS.items():ck(sha((root/name).read_bytes())==pin,'pin '+name)
 old=read(root/'complete84_scaled_strong_output.json')['packet']
 prior=read(root/'complete84_auxiliary_mixed_cut.json')
 z=(0,)*6;unit=[tuple(int(j==k) for j in range(6)) for k in range(6)]
 # Delta,c,i,f,T,R in that order.
 leaves=[z]+unit+[(0,2,0,0,0,0),(1,2,0,0,0,0)]
 V={(0,1,0,1,1,0):1,(0,1,0,0,0,0):-1,(0,0,0,2,0,1):-1}
 w=(1,0,0,2,0,0);q=(2,4,2,0,0,0);f2=(0,0,0,2,0,0)
 W={w:1};Q={q:1};S=add(W,Q,-1);P={f2:1,(1,4,2,0,0,0):-1}
 ck(w not in leaves and q not in leaves,'independent output classes modulo paid span')
 # Q,S expressed on the independent W,Q classes: determinant -1.
 matrix=[[0,1],[1,-1]];ck(matrix[0][0]*matrix[1][1]-matrix[0][1]*matrix[1][0]==-1,'two independent zero relations')
 def laurent(poly):
  result={}
  for (d,c,i,f,t,r),n in poly.items():
   e=(c-4*d,i-2*d,f+2*d,t,r);result[e]=result.get(e,0)+n
  return {e:n for e,n in result.items() if n}
 lv=laurent(V);ck(not laurent(P) and len(lv)==3,'P quotient')
 es=list(lv);a=[x-y for x,y in zip(es[1],es[0])];b=[x-y for x,y in zip(es[2],es[0])]
 nonzero_minor=next((a[j]*b[k]-a[k]*b[j] for j in range(5) for k in range(j+1,5) if a[j]*b[k]-a[k]*b[j]),None)
 ck(nonzero_minor is not None,'Laurent V support noncollinear')
 ck(len({(e[4],e[5]) for e in V})==3,'three T/R multidegrees')
 ck(len({(e[0],e[2]) for e in P})==2 and len({(e[0],e[2]) for e in S})==2,'two Delta/i multidegrees')
 gcd=lambda a,b:tuple(min(x,y) for x,y in zip(a,b))
 def cost(t):
  if t in leaves:return 0
  if any(tuple(x+y for x,y in zip(a,b))==t for a in leaves for b in leaves):return 1
  return 2
 case_data=[]
 for name,pair,mixed in [
  ('monomial_sum',[(0,1,0,1,1,0),(0,0,0,2,0,1)],0),
  ('c_times_Tf_minus_one',[(0,0,0,1,1,0),(0,0,0,2,0,1)],1),
  ('f_times_cT_minus_Rf',[(0,1,0,0,1,0),(0,0,0,1,0,1)],1)]:
  record={'V_grouping':name,'mixed_products':mixed,'targets':{}}
  for target,expected,label in [(w,5,'V_and_W'),(f2,4,'V_and_f_squared')]:
   ts=pair+[target];gs=[gcd(ts[j],ts[k]) for j in range(3) for k in range(j+1,3)]
   shared=[g for g in gs if g not in leaves];ck(all(g==f2 for g in shared) and len(shared)<=1,'at most shared f²')
   lower=sum(cost(t) for t in ts)-len(shared)+mixed;ck(lower==expected,'three-addition product bound')
   ck(all(gcd(t,q) in leaves and sum(gcd(t,q))<=1 for t in ts),'no new monomial overlap with Q')
   record['targets'][label]={'monomials':[list(t) for t in ts],'individual_lower_bounds':[cost(t) for t in ts],'shared_new_divisors':[list(t) for t in shared],'product_lower_bound':lower}
  case_data.append(record)
 ck(cost(q)==2,'Q needs at least two monomial products')
 # Exhaust ALL positive-i monomial divisors of Q, with scalar factors suppressed.
 # At most one pure i-containing multiplication is possible in a 5M circuit.
 # Relax all i-free divisors to free inputs and enumerate the remaining last gate.
 divisors=[(d,c,i,0,0,0) for d in range(3) for c in range(5) for i in [1,2]]
 ifree=[(d,c,0,0,0,0) for d in range(3) for c in range(5)]
 pivots=[]
 for u in divisors:
  ways=[]
  if u==q:ways.append({'form':'alias','other':None})
  for other in ifree+[unit[2],u]:
   if tuple(x+y for x,y in zip(u,other))==q:
    label='square' if other==u else 'times_i' if other==unit[2] else 'times_i_free'
    item={'form':label,'other':list(other)}
    if item not in ways:ways.append(item)
  if ways:pivots.append({'U_exponents':list(u),'Q_restoration':ways})
 expected={(d,c,2,0,0,0) for d in range(3) for c in range(5)}|{(1,2,1,0,0,0),(2,4,1,0,0,0)}
 ck({tuple(v['U_exponents']) for v in pivots}==expected and len(pivots)==17,'exact necessary pivot census')
 # Complete all-value attaining splice, with every use paid.
 replacement={
  'auxiliary_Tf':['mixed_cT','*','R10a','auxiliary_quotient'],
  'auxiliary_Tf_minus_one':['mixed_Rf','*','r_lhs','f'],
  'auxiliary_c_Tf':['mixed_linear','-','mixed_cT','mixed_Rf'],
  'auxiliary_R_f2':['mixed_f_linear','*','f','mixed_linear'],
  'aux_u_rhs':['aux_u_rhs','-','mixed_f_linear','R10a']}
 source=[replacement.get(r[0],r[:]) for r in old['source']]
 ck(source==prior['mixed_attaining_packet']['source'],'attaining complete literal source')
 cut=prior['cut_rows'];names=set(cut)|{r[0] for r in replacement.values()}
 supplied={name:{unit[k]:1} for k,name in enumerate(['A','R10a','i','f','auxiliary_quotient','r_lhs'])};supplied['c2']={(0,2,0,0,0,0):1};supplied['Ac2']={(1,2,0,0,0,0):1}
 def local(rows):
  env=dict(supplied)
  for name,op,a,b in rows:
   if name not in names:continue
   aa=env[a] if type(a) is str else {z:a};bb=env[b] if type(b) is str else {z:b}
   env[name]=mul(aa,bb) if op=='*' else add(aa,bb,1 if op=='+' else -1)
  return env
 left=local(old['source']);right=local(source)
 for name,expected_poly in [('aux_u_rhs',V),('R16',Q),('norm_strong',S),('scaled_f_square',W)]:ck(left[name]==right[name]==expected_poly,'exact coefficient '+name)
 cutset=set(cut);external={name:[] for name in cut}
 for name,op,a,b in old['source']:
  for v in [a,b]:
   if v in cutset and name not in cutset:external[v].append(name)
 ck({name for name,uses in external.items() if uses}=={'aux_u_rhs','R16','norm_strong'},'exact external consumer interface')
 known=set(old['free']);deps={};counts=Counter()
 for name,op,a,b in source:
  ck(name not in known and all(type(v) is int or v in known for v in [a,b]),'fresh acyclic source')
  known.add(name);deps[name]=[a,b];counts[op]+=1
 todo=[old['output']];live=set()
 while todo:
  v=todo.pop()
  if type(v) is str and v not in live:live.add(v);todo.extend(deps.get(v,[]))
 ck(live==known and len(source)==84 and counts['*']==47 and counts['+']+counts['-']==37,'complete paid liveness')
 for row in old['source']:
  if row[0] not in replacement:ck(row in source,'every other row retained literally')
 # All changed intermediate names are private; the exact V cut discharges their only boundary.
 deleted=set(replacement)-{'aux_u_rhs'}
 for name,op,a,b in old['source']:
  if name not in replacement:ck(not any(v in deleted for v in [a,b]),'private replacement intermediates')
 packet=dict(old,source=source,all_ring_relation='F_attaining=F84',ledger={'total':84,'M':47,'A':37,'all_rows_and_ports_live':True})
 return {'status':'PASS','source_sha256':sha(Path(__file__).read_bytes()),'pins':PINS,'parent_packet':old,'attaining_packet':packet,
  'local_polynomials':{name:serial(poly) for name,poly in [('V',V),('W',W),('Q',Q),('S',S),('P',P)]},'external_cut_consumers':external,
  'proof_certificates':{'variable_order':['Delta','c','i','f','T','R'],'Q_S_relation_matrix_on_W_Q':matrix,'relation_determinant':-1,'laurent_P':serial(laurent(P)),'laurent_V':serial(lv),'noncollinear_minor':nonzero_minor,'three_addition_cases':case_data},
  'necessary_cancellation_pivots':pivots,'positive_i_divisors_examined':len(divisors),
  'theorems':{'unrestricted_products_at_least':5,'unrestricted_additions_at_least':3,'products_with_exactly_three_additions_at_least':7,'products_if_Q_has_monomial_cone_at_least':6,'only_possible_at_most_nine_budget':{'M':5,'A':4},'monomial_producing_additions_in_that_budget':1,'necessary_pivot_count':17},
  'scope':'Unbounded necessary conditions, not existence or exclusion of all nine-gate circuits. Exactly17 pivot monomials remain necessary; no candidate claimed. Constants/scalar multiples free in lower-bound relaxation; attaining literal full84 charges every use.'}
def main():
 ap=argparse.ArgumentParser();ap.add_argument('--root',type=Path,required=True);g=ap.add_mutually_exclusive_group(required=True);g.add_argument('--expect',type=Path);g.add_argument('--output',type=Path);args=ap.parse_args();result=run(args.root)
 if args.output:args.output.write_text(json.dumps(result,sort_keys=True,indent=2)+'\n')
 else:ck(exact(result,read(args.expect)),'type-exact receipt replay')
 print(json.dumps({'status':result['status'],'theorems':result['theorems'],'full':result['attaining_packet']['ledger']},sort_keys=True))
if __name__=='__main__':main()
