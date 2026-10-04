#!/usr/bin/env python3
"""Inert-source audit for a mixed auxiliary producer lower bound."""
import argparse
import hashlib
import itertools
import json
from collections import Counter
from pathlib import Path

PINS = {
 'complete84_scaled_strong_output.py':'8b4dd58c849ae79751f1be6638f1b9e3f9072a714c5479eadf1039f10d0c7737',
 'complete84_scaled_strong_output.json':'8b2bc5d0b4db90c168107b7ded2cb4ca08df0098ed190851a3db4f1e49a9c0cf',
 'complete84_scaled_strong_output.md':'01eb7df6688c08c6788a3c7a1cc272ca5ffc1a87734fd622dbec8a64ae974ade',
 'complete84_auxiliary_monomial_scaling.py':'643ca33730e8b1e43088240c8f81dd72fbb6dc87506206c55ab5fda411bf2390',
 'complete84_auxiliary_monomial_scaling.json':'851d6339e1e8ab940f977b9177eef804fa6f45601c06f974412d0567267c4ae1',
 'complete84_auxiliary_monomial_scaling.md':'db05c735b61b3165897430ed78f9a2d3967beb8f3c89044e7d5a29d4a9d79ffe',
}
def ck(test, message):
 if not test: raise ValueError(message)
def digest(data): return hashlib.sha256(data).hexdigest()
def read_json(path):
 def pairs(items):
  result={}
  for key,value in items:
   ck(key not in result,'duplicate JSON key');result[key]=value
  return result
 def bad(value): raise ValueError('nonfinite JSON')
 return json.loads(path.read_text(),object_pairs_hook=pairs,parse_constant=bad)
def exact(a,b):
 if type(a) is not type(b): return False
 if isinstance(a,dict): return a.keys()==b.keys() and all(exact(a[k],b[k]) for k in a)
 if isinstance(a,list): return len(a)==len(b) and all(exact(x,y) for x,y in zip(a,b))
 return a==b
def add(a,b,sign=1):
 r=dict(a)
 for e,c in b.items():
  r[e]=r.get(e,0)+sign*c
  if not r[e]: del r[e]
 return r
def mul(a,b):
 r={}
 for e,c in a.items():
  for f,d in b.items():
   g=tuple(x+y for x,y in zip(e,f));r[g]=r.get(g,0)+c*d
 return {e:c for e,c in r.items() if c}
def serial(p): return [[list(e),c] for e,c in sorted(p.items())]
def run(root):
 for name,pin in PINS.items(): ck(digest((root/name).read_bytes())==pin,'pin '+name)
 packet=read_json(root/'complete84_scaled_strong_output.json')['packet']
 rows=packet['source'];by={r[0]:r for r in rows};free=packet['free']
 cut=['L16','auxiliary_Tf','auxiliary_Tf_minus_one','auxiliary_c_Tf','auxiliary_R_f2','aux_u_rhs','aux_coefficient_root','R16','scaled_f_square','norm_strong']
 definitions=[['*','f','f'],['*','auxiliary_quotient','f'],['-','auxiliary_Tf',1],['*','R10a','auxiliary_Tf_minus_one'],['*','r_lhs','L16'],['-','auxiliary_c_Tf','auxiliary_R_f2'],['*','i','Ac2'],['*','aux_coefficient_root','aux_coefficient_root'],['*','A','L16'],['-','scaled_f_square','R16']]
 for name,expr in zip(cut,definitions): ck(by[name][1:]==expr,'literal cut '+name)
 ck(by['c2'][1:]==['*','R10a','R10a'] and by['Ac2'][1:]==['*','A','c2'],'dependent paid ports')
 consumers={name:[] for name in cut}
 for n,op,a,b in rows:
  for v in (a,b):
   if v in consumers: consumers[v].append(n)
 external={n:[c for c in cs if c not in cut] for n,cs in consumers.items()}
 ck({n for n,cs in external.items() if cs}=={'aux_u_rhs','R16','norm_strong'},'full external interface')
 replacement={
  'auxiliary_Tf':['mixed_cT','*','R10a','auxiliary_quotient'],
  'auxiliary_Tf_minus_one':['mixed_Rf','*','r_lhs','f'],
  'auxiliary_c_Tf':['mixed_linear','-','mixed_cT','mixed_Rf'],
  'auxiliary_R_f2':['mixed_f_linear','*','f','mixed_linear'],
  'aux_u_rhs':['aux_u_rhs','-','mixed_f_linear','R10a'],
 }
 changed=[replacement.get(r[0],r[:]) for r in rows]
 zero=(0,)*6;units=[tuple(int(k==j) for k in range(6)) for j in range(6)]
 # Order Delta,c,i,f,T,R, including the two actual dependent monomials.
 ports=['A','R10a','i','f','auxiliary_quotient','r_lhs']
 paid={n:{units[j]:1} for j,n in enumerate(ports)}
 paid['c2']={(0,2,0,0,0,0):1};paid['Ac2']={(1,2,0,0,0,0):1}
 names=set(cut)|{r[0] for r in replacement.values()}
 def local(source):
  env=dict(paid)
  for n,op,a,b in source:
   if n not in names: continue
   aa=env[a] if type(a) is str else {zero:a};bb=env[b] if type(b) is str else {zero:b}
   env[n]=mul(aa,bb) if op=='*' else add(aa,bb,1 if op=='+' else -1)
  return env
 before=local(rows);after=local(changed)
 for n in ['L16','aux_u_rhs','aux_coefficient_root','R16','scaled_f_square','norm_strong']:
  ck(before[n]==after[n],'exact local identity '+n)
 V={(0,1,0,1,1,0):1,(0,1,0,0,0,0):-1,(0,0,0,2,0,1):-1}
 W={(1,0,0,2,0,0):1};Q={(2,4,2,0,0,0):1}
 ck(before['aux_u_rhs']==V and before['scaled_f_square']==W and before['R16']==Q,'target formulas')
 # Full graph equivalence: only V is substituted by its proved identical polynomial.
 def interning(source,table):
  env={n:('free',n) for n in free}
  for n,op,a,b in source:
   if n=='aux_u_rhs': env[n]=('equal_cut','V');continue
   aa=env[a] if type(a) is str else ('integer',a);bb=env[b] if type(b) is str else ('integer',b)
   key=(op,aa,bb)
   if key not in table: table[key]=len(table)
   env[n]=table[key]
  return env
 intern={};oldvalues=interning(rows,intern);newvalues=interning(changed,intern)
 for n in by:
  if n not in replacement: ck(oldvalues[n]==newvalues[n],'unchanged whole-source value '+n)
 ck(oldvalues[packet['output']]==newvalues[packet['output']],'full all-ring identity')
 def audit(source):
  known=set(free);deps={};counts=Counter()
  for n,op,a,b in source:
   ck(n not in known and op in ['+','-','*'],'fresh legal row')
   ck(all(type(v) is int or type(v) is str and v in known for v in (a,b)),'closure')
   known.add(n);deps[n]=[a,b];counts[op]+=1
  todo=[packet['output']];live=set()
  while todo:
   v=todo.pop()
   if type(v) is str and v not in live: live.add(v);todo.extend(deps.get(v,[]))
  ck(live==known,'whole row and port liveness')
  return {'M':counts['*'],'A':counts['+']+counts['-'],'total':len(source),'live_rows':len(deps),'live_ports':len(free)}
 ledgers=[audit(s) for s in [rows,changed]]
 ck(all(d['M']==47 and d['A']==37 and d['total']==84 for d in ledgers),'full ledgers')
 # Exact determinant polynomial for the Hessian of cT-Rf-lambda*c².
 C=lambda n:{(0,):n} if n else {}
 Lam={(1,):-2}
 H=[[Lam,C(1),{},{}],[C(1),{},{},{}],[{},{},{},C(-1)],[{},{},C(-1),{}]]
 determinant={}
 for p in itertools.permutations(range(4)):
  inversions=sum(p[j]>p[k] for j in range(4) for k in range(j+1,4));term=C((-1)**inversions)
  for j,k in enumerate(p): term=mul(term,H[j][k])
  determinant=add(determinant,term)
 ck(determinant==C(1),'rank4 for every lambda')
 # Primitive linear-polynomial conditions and the Laurent quotient certificate.
 gcd=lambda a,b:tuple(min(x,y) for x,y in zip(a,b))
 ck(gcd((0,1,0,1,0,0),gcd((0,1,0,0,0,0),(0,0,0,2,0,1)))==zero,'V primitive in T')
 P={(0,0,0,2,0,0):1,(1,4,2,0,0,0):-1}
 ck(gcd((0,0,0,2,0,0),(0,4,2,0,0,0))==zero,'P primitive in Delta')
 def quotient(p):
  result={}
  for (d,c,i,f,t,r),coef in p.items():
   e=(c-4*d,i-2*d,f+2*d,t,r);result[e]=result.get(e,0)+coef
  return {e:c for e,c in result.items() if c}
 ck(not quotient(P) and len(quotient(V))==3,'Laurent quotient nonmonomial obstruction')
 exps=list(V);diffs=[[x-y for x,y in zip(e,exps[0])] for e in exps[1:]]
 minors=[diffs[0][j]*diffs[1][k]-diffs[0][k]*diffs[1][j] for j in range(6) for k in range(j+1,6)]
 ck(any(minors),'V support noncollinear')
 leaves=[zero]+units+[(0,2,0,0,0,0),(1,2,0,0,0,0)]
 def first_cost(t):
  if t in leaves: return 0
  if any(tuple(x+y for x,y in zip(a,b))==t for a in leaves for b in leaves): return 1
  return 2 # Only a >=2 lower bound; attainment is separately supplied.
 cases=[
  ('monomial_sum',[(0,1,0,1,1,0),(0,0,0,2,0,1),(1,0,0,2,0,0)],0,1),
  ('c_times_Tf_minus_one',[(0,0,0,1,1,0),(0,0,0,2,0,1),(1,0,0,2,0,0)],1,1),
  ('f_times_cT_minus_Rf',[(0,1,0,0,1,0),(0,0,0,1,0,1),(1,0,0,2,0,0)],1,0),
 ]
 case_data=[]
 for name,targets,mixed,sharing in cases:
  gs=[gcd(targets[j],targets[k]) for j in range(3) for k in range(j+1,3)]
  unpaid=[g for g in gs if g not in leaves]
  ck(unpaid==([(0,0,0,2,0,0)] if sharing else []),'only possible shared new divisor')
  costs=[first_cost(t) for t in targets];lower=sum(costs)-sharing+mixed
  ck(lower==5,'five products with two additions')
  case_data.append({'case':name,'targets':[list(t) for t in targets],'individual_product_lower_bounds':costs,'pairwise_gcds':[list(g) for g in gs],'at_most_one_shared_f_squared':bool(sharing),'mixed_products':mixed,'product_lower_bound':lower})
 # Supplementary evaluations exercise the whole source, not positive compiler zeros.
 def value(source,values):
  env=dict(values)
  for n,op,a,b in source:
   aa=env[a] if type(a) is str else a;bb=env[b] if type(b) is str else b
   env[n]=aa*bb if op=='*' else aa+bb if op=='+' else aa-bb
  return env[packet['output']]
 evaluations=[]
 for k in range(12):
  values={n:((k+3)*(j+2)+j*j)%9-4 for j,n in enumerate(free)}
  v=value(rows,values);ck(v==value(changed,values),'supplementary full signed check')
  evaluations.append({'values':values,'output_sha256':digest(str(v).encode())})
 mixed=dict(packet,source=changed,all_ring_relation='F_mixed=F84',ledger=ledgers[1])
 return {'status':'PASS','source_sha256':digest(Path(__file__).read_bytes()),'parent_pins':PINS,
  'parent_packet':packet,'mixed_attaining_packet':mixed,'cut_rows':cut,'cut_consumers':consumers,'cut_external_consumers':external,
  'cut_ledger':{'M':7,'A':3,'total':10},'full_ledgers':ledgers,
  'exact_cut_polynomials':{n:serial(before[n]) for n in ['aux_u_rhs','R16','scaled_f_square','norm_strong']},
  'proof_certificates':{'variable_order':['Delta','c','i','f','T','R'],'hessian_determinant':serial(determinant),'laurent_P':serial(quotient(P)),'laurent_V':serial(quotient(V)),'support_noncollinear_minor':next(v for v in minors if v),'two_addition_groupings':case_data},
  'theorems':{'V_products_at_least':3,'joint_V_W_products_at_least':4,'joint_V_W_additions_at_least':2,'joint_V_W_products_if_two_additions_at_least':5,'joint_V_W_total_at_least':7,'joint_V_Q_S_additions_at_least':3,'protected_Q_and_final_S_total_at_least':10},
  'supplementary_signed_evaluations':evaluations,
  'scope':'Unrestricted mixed V,W lower bound with actual dependent paid monomials; ten-gate bound retains exact two Q producers and final S=W-Q. General interleaved Q or changed strong/output coordinates are not excluded; no global84 lower bound.'}
def main():
 ap=argparse.ArgumentParser();ap.add_argument('--root',type=Path,required=True)
 g=ap.add_mutually_exclusive_group(required=True);g.add_argument('--expect',type=Path);g.add_argument('--output',type=Path)
 args=ap.parse_args();result=run(args.root)
 if args.output: args.output.write_text(json.dumps(result,sort_keys=True,indent=2)+'\n')
 else: ck(exact(result,read_json(args.expect)),'type-exact receipt replay')
 print(json.dumps({'status':result['status'],'cut':result['cut_ledger'],'full':result['full_ledgers'][1],'theorems':result['theorems']},sort_keys=True))
if __name__=='__main__':main()
