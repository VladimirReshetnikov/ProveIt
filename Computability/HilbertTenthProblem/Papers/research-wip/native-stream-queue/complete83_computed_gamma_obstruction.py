#!/usr/bin/env python3
"""Finite acyclic computed-wire reuse census; no predecessor execution."""
import argparse,hashlib,json
from pathlib import Path
from fractions import Fraction
from collections import Counter
PINS={
'complete84_scaled_strong_output.py':'8b4dd58c849ae79751f1be6638f1b9e3f9072a714c5479eadf1039f10d0c7737',
'complete84_scaled_strong_output.json':'8b2bc5d0b4db90c168107b7ded2cb4ca08df0098ed190851a3db4f1e49a9c0cf',
'complete84_scaled_strong_output.md':'01eb7df6688c08c6788a3c7a1cc272ca5ffc1a87734fd622dbec8a64ae974ade',
'complete83_direct_gamma_witness_obstruction.py':'32994d28509f606d4bf149ac95eef9b3be468f89265012dd246a2c70b29fbc79',
'complete83_direct_gamma_witness_obstruction.json':'b7cbbda6885dcb9495a105e0a3427f2114f042344f257fa9ae76bc7cbcd4450f',
'complete83_direct_gamma_witness_obstruction.md':'c1f7a146ba85020ea1ed436e64de9a9163f9c5c7ac8d013d46d719ccef92d3f4',
'complete83_independent_gamma_scout.md':'bdbcc3be5396bced89373da5ffb30f0f3f113f7e8e7ebe65e4f7b730264f1b41',
'review_complete85_auxiliary_bezout_math.md':'77a4071be471db23642cabddc5bd4880debfa53441bf3640c3c45523e9bdb36d',
'complete83_multiplicative_gamma_obstruction.md':'012ba873b2cc4936e4d8865837a101d997b877dcc03e61c801cdb0cf010e527a',
}
GROUPS={
'outer_below_a':'repunit q Lbig n2 wn2 sn2 UM R12 q_minus_F q_minus_FZ C_after_alpha scaled_t marked_rhs W odd_index index_difference gap_product gap Lm1 rproduct qMF mask_factor mask r_lhs kinner innerC transport_partial local_rhs'.split(),
'polynomial_below_previous_Pell':'a4 a4m5 a_square A norm_strong'.split(),
'unit_factors':'norm_first norm_input norm_aux norm_index norm_transport'.split(),
'first_ratio_larger':'tau_square R10b ksn2 first_root_base first_next first_product R10a cam2 D1 hpm1'.split(),
'large_main_strong_auxiliary':'c2 Ac2 aux_y2 L16 auxiliary_Tf auxiliary_Tf_minus_one auxiliary_c_Tf auxiliary_R_f2 aux_u_rhs H2 aux_coefficient_root R16 scaled_f_square'.split(),
'negative_auxiliary':'aux_square_gap L17'.split(),
'input_coefficient_gap':'index_product index_rhs difference_multiple exponent_partial exponent_rhs mu2 kappa2 scaled_kappa2'.split(),
'multiplicative_subfamily':['modulus_multiple'],
}
def need(v,s):
 if not v:raise ValueError(s)
def sha(b):return hashlib.sha256(b).hexdigest()
def exact(a,b):
 if type(a)is not type(b):return False
 if isinstance(a,dict):return a.keys()==b.keys() and all(exact(a[k],b[k]) for k in a)
 if isinstance(a,list):return len(a)==len(b) and all(exact(u,v) for u,v in zip(a,b))
 return a==b
def read(p):
 def pairs(xs):
  d={}
  for k,v in xs:need(k not in d,'duplicate key');d[k]=v
  return d
 def bad(x):raise ValueError('noninteger JSON '+x)
 return json.loads(p.read_text(),object_pairs_hook=pairs,parse_float=bad,parse_constant=bad)
def pc(n):return {():n} if n else {}
def pv(n):return {(n,):1}
def pa(a,b,sign=1):
 d=a.copy()
 for m,c in b.items():d[m]=d.get(m,0)+sign*c
 return {m:c for m,c in d.items() if c}
def pm(a,b):
 d={}
 for m,c in a.items():
  for n,e in b.items():
   k=tuple(sorted(m+n));d[k]=d.get(k,0)+c*e
 return {m:c for m,c in d.items() if c}
def phash(p):return sha(json.dumps([[list(m),c] for m,c in sorted(p.items())],separators=(',',':')).encode())
def cut_identities():
 a,c,H,X,G,W,rho,k=[pv(n) for n in ['a','c','H','X','G','W','rho','k']]
 A=pa(pm(a,a),H)
 D=pa(pa(X,pm(a,c)),pm(G,H));main=pa(pm(D,D),pm(A,pm(c,c)),-1)
 t=pa(X,pm(G,H));want=pa(pa(pm(t,t),pm(pc(2),pm(pm(a,c),t))),pm(H,pm(c,c)),-1)
 need(main==want,'exact main cancellation')
 mu=pa(pa(W,pm(a,k)),pm(rho,H));inp=pa(pm(mu,mu),pm(A,pm(k,k)),-1)
 v=pa(W,pm(rho,H));target=pa(pa(pm(v,v),pm(pc(2),pm(pm(a,k),v))),pm(H,pm(k,k)),-1)
 need(inp==target,'exact input cancellation')
 return {'main_terms':len(main),'main_sha256':phash(main),'input_terms':len(inp),'input_sha256':phash(inp)}
# Highest homogeneous components. The only cancelled leading levels are handled
# by the two complete formal identities certified above, not guessed by weights.
def ladd(a,b,sign=1):
 if a[0]>b[0]:return a
 if b[0]>a[0]:return b if sign==1 else (b[0],{m:-v for m,v in b[1].items()})
 p=pa(a[1],b[1],sign);need(p,'unexpected leading cancellation');return a[0],p
def lmul(a,b):return a[0]+b[0],pm(a[1],b[1])
def leaders(packet,wire):
 env={v:(0 if v in packet['fixed_numerals'] else 1,pv(v)) for v in packet['free']}
 def val(a):return (0,pc(a)) if type(a)is int else env[a]
 for out,op,a,b in packet['source']:
  if out=='norm_main':
   aa=env['R12'];cc=env['R10a'];H=env['a4m5'];X=env['wn2'];G=env[wire]
   v=ladd(X,lmul(G,H))
   env[out]=ladd(ladd(lmul(v,v),lmul((0,pc(2)),lmul(lmul(aa,cc),v))),lmul(H,lmul(cc,cc)),-1)
  elif out=='norm_input':
   aa=env['R12'];kk=env['index_rhs'];H=env['a4m5'];v=ladd(env['W'],lmul(env['rho'],H))
   env[out]=ladd(ladd(lmul(v,v),lmul((0,pc(2)),lmul(lmul(aa,kk),v))),lmul(H,lmul(kk,kk)),-1)
  else:env[out]=lmul(val(a),val(b)) if op=='*' else ladd(val(a),val(b),1 if op=='+' else -1)
 return env

def audit(p):
 seen=set(p['free']);by={};degree={v:0 if v in p['fixed_numerals'] else 1 for v in p['free']}
 for out,op,a,b in p['source']:
  need(out not in seen and op in ['+','-','*'],'fresh valid row')
  need(all(type(v)is int or type(v)is str and v in seen for v in (a,b)),'topological closure')
  da=0 if type(a)is int else degree[a];db=0 if type(b)is int else degree[b]
  degree[out]=da+db if op=='*' else max(da,db);seen.add(out);by[out]=(a,b)
 live=set();todo=[p['output']]
 while todo:
  v=todo.pop()
  if type(v)is not str or v in live:continue
  live.add(v);todo.extend(by.get(v,()))
 need(seen<=live,'all rows and free ports live')
 c=Counter(r[1] for r in p['source']);need(c['*']==47 and c['+']+c['-']==36 and len(by)==83,'full cost')
 return {'M':47,'A':36,'total':83,'witnesses':len(p['witnesses']),'naive_degree_upper':degree[p['output']]}
def evaluate(rows,values):
 e=values.copy()
 for out,op,a,b in rows:
  aa=a if type(a)is int else e[a];bb=b if type(b)is int else e[b]
  e[out]=aa*bb if op=='*' else aa+bb if op=='+' else aa-bb
 return e

def make(root):
 for f,pin in PINS.items():need(sha((root/f).read_bytes())==pin,'pin '+f)
 original=read(root/'complete84_scaled_strong_output.json');parent=original['packet'];rows=parent['source']
 need(original['source_sha256']==PINS['complete84_scaled_strong_output.py'],'parent source pin')
 need([r[0] for r in rows if 'gamma_sum' in r[2:]]==['gam'],'private gamma consumer')
 need([r[0] for r in rows if 'sigma' in r[2:]]==['gamma_sum'],'private sigma consumer')
 dependent={'gamma_sum'}
 for r in rows:
  if any(v in dependent for v in r[2:] if type(v)is str):dependent.add(r[0])
 candidates=[r[0] for r in rows if r[0] not in dependent]
 groups={v:k for k,vs in GROUPS.items() for v in vs}
 need(len(candidates)==72 and len(groups)==72 and set(candidates)==set(groups),'complete acyclic grammar coverage')
 need(sum(map(len,GROUPS.values()))==72,'no duplicate grouping')
 packets={};counts=Counter();checks=registers=0
 for wire in candidates:
  todo=[]
  for r in rows:
   if r[0]=='gamma_sum':continue
   row=r.copy()
   if r[0]=='gam':row[2]=wire
   todo.append(row)
  source=[];seen=set(parent['free'])-{'sigma'}
  while todo:
   ready=next((j for j,r in enumerate(todo) if all(type(v)is int or v in seen for v in r[2:])),None)
   need(ready is not None,'acyclic candidate');row=todo.pop(ready);source.append(row);seen.add(row[0])
  p={k:parent[k] for k in ['fixed_numerals','ordinary_input','output','factors']}
  p.update({'free':[v for v in parent['free'] if v!='sigma'],'witnesses':[v for v in parent['witnesses'] if v!='sigma'],'source':source,'alias':wire,'obstruction_group':groups[wire],'domain':'All 17 supplied witnesses and x strictly positive integers; inherited valid fixed compiler numerals.','all_ring_pullback':'P_child=P84(sigma_old='+wire+'-rho); selected wire is independent of gamma_sum.'})
  p['ledger']=audit(p);need(len(p['witnesses'])==17,'arity')
  lead=leaders(p,wire);d,poly=lead[p['output']]
  ds=[lead[f][0] for f in p['factors']]
  need(ds[0]==22 and ds[2:]==[32,60,7,2,46] and d==sum(ds),'all factor degree sum')
  wd=lead[wire][0];md=max(wd+17,2*wd+12)
  need(ds[1]==md and d==169+md,'wire-dependent degree formula')
  p['degree']={'selected_wire_degree':wd,'factor_degrees':ds,'exact_degree':d,'full_leader_terms':len(poly),'full_leader_powers':[[[[n,e] for n,e in sorted(Counter(m).items())],v] for m,v in sorted(poly.items())],'full_leader_sha256':phash(poly),'scope':'Highest homogeneous source interpretation, using the exact main/input cancellation identities; companion proves nonvanishing on every valid fixed-numeral slice.'};counts[d]+=1
  for seed in range(4):
   values={v:Fraction(((i+3)*(seed+2)%13)-6,1+(seed%2)) for i,v in enumerate(parent['free'])}
   e=evaluate(rows,values);values['sigma']=e[wire]-values['rho'];old=evaluate(rows,values);child=evaluate(source,{k:v for k,v in values.items() if k!='sigma'})
   need(all(old[r[0]]==child[r[0]] for r in source),'full signed/rational register pullback')
   checks+=1;registers+=len(source)
  packets[wire]=p
 # Fresh Pell components corroborate strict native gap inequalities only.
 components=[]
 for A in (6,10,18,26):
  cs=[0,1];Ds=[1,A]
  for n in range(2,16):cs.append(2*A*cs[-1]-cs[-2]);Ds.append(2*A*Ds[-1]-Ds[-2])
  for R in (7,11,15):
   a=A-2;H=4*A-5;X=2;G=Fraction(Ds[R]-a*cs[R]-X,H);l=(R-1)//2;D=A*A-1
   need(cs[R-1]<G<2*Fraction(cs[R],H),'quotient sandwich component')
   need(cs[l]**2<G<cs[l+1]**2,'coefficient-square gap component')
   need(D*cs[l-1]**2+1<G<D*cs[l]**2,'norm-square gap component')
   need(Ds[R-2]<G<Ds[R-1],'root gap component')
   need(a*cs[R-2]+1<G<a*cs[R-1]-1,'linear coefficient gap component')
   components.append({'A':A,'R':R,'X':X,'Gamma_numerator':G.numerator,'Gamma_denominator':G.denominator})
 return {'schema':'complete83-computed-gamma-obstruction-v1','status':'PASS_FINITE_ACYCLIC_REUSE_GRAMMAR_EMPTY_ON_VALID_COMPILER_SLICES','source_sha256':sha(Path(__file__).read_bytes()),'pins':PINS,'predecessor_execution':False,'dependent_excluded':sorted(dependent),'candidate_count':72,'obstruction_groups':GROUPS,'packets':packets,'cut_identities':cut_identities(),'exact_degree_histogram':{str(k):v for k,v in sorted(counts.items())},'total_saved_gates':72*83,'full_signed_rational_assignments':checks,'retained_register_equalities':registers,'Pell_gap_components':components,'scope':'All computed wires of the fixed84 DAG outside the gamma_sum dependency cone. No new expression, extra producer, changed fixed numerals, input shift or arbitrary circuit claim. Every saved form is rejected, not a universal bound.'}

def main():
 a=argparse.ArgumentParser(description=__doc__);a.add_argument('--root',type=Path,required=True);g=a.add_mutually_exclusive_group(required=True);g.add_argument('--output',type=Path);g.add_argument('--expect',type=Path);v=a.parse_args();out=make(v.root)
 if v.output:
  with v.output.open('x') as f:json.dump(out,f,sort_keys=True,indent=2);f.write('\n')
 else:need(exact(out,read(v.expect)),'type-exact receipt replay')
 print('PASS: 72 full 83-gate acyclic computed-wire sources; all excluded on valid compiler slices')
if __name__=='__main__':main()
