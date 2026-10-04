#!/usr/bin/env python3
"""Fresh source-binding and symbolic corroboration; predecessors are inert bytes."""
import argparse
import hashlib
import json
from collections import Counter
from pathlib import Path

PINS = {
 'complete84_scaled_strong_output.py':'8b4dd58c849ae79751f1be6638f1b9e3f9072a714c5479eadf1039f10d0c7737',
 'complete84_scaled_strong_output.json':'8b2bc5d0b4db90c168107b7ded2cb4ca08df0098ed190851a3db4f1e49a9c0cf',
 'complete84_scaled_strong_output.md':'01eb7df6688c08c6788a3c7a1cc272ca5ffc1a87734fd622dbec8a64ae974ade',
 'first_norm_monomial_scaling_bound.py':'8f938efc5e1690d173bd9524cf83b60d3b78b2146be11593771632f44b0a3f58',
 'first_norm_monomial_scaling_bound.json':'b687e870b6a841f178c238399688f42ddd43640692d034526cf6b15b6a63c238',
 'first_norm_monomial_scaling_bound.md':'1a7677200ada8b171268aeb5189a9477dc2c9a3743fffb6e1f4d3de11dd3be4c',
 'first_norm_five_gate_lower_bound.md':'3f7580635b63b6cc7bda27b23022db99c85fdc4341c34ea1fb5d55f42e00c2fc',
}
def need(ok,msg):
 if not ok:raise ValueError(msg)
def sha(x):return hashlib.sha256(x).hexdigest()
def canon(x):return json.dumps(x,sort_keys=True,separators=(',',':')).encode()
def read(path):
 def pairs(xs):
  out={}
  for k,v in xs:
   need(k not in out,'duplicate key');out[k]=v
  return out
 def bad(x):raise ValueError('noninteger JSON '+x)
 return json.loads(path.read_text(),object_pairs_hook=pairs,parse_float=bad,parse_constant=bad)
def atom(x):return {():x} if type(x)is int and x else {} if type(x)is int else {(x,):1}
def add(a,b,s=1):
 out=dict(a)
 for m,c in b.items():out[m]=out.get(m,0)+s*c
 return {m:c for m,c in out.items() if c}
def mul(a,b):
 out={}
 for m,c in a.items():
  for n,d in b.items():
   k=tuple(sorted(m+n));out[k]=out.get(k,0)+c*d
 return {m:c for m,c in out.items() if c}
def power(a,n):
 out=atom(1)
 for _ in range(n):out=mul(out,a)
 return out
def sub(p,bindings):
 out={}
 for m,c in p.items():
  term=atom(c)
  for v in m:term=mul(term,bindings.get(v,atom(v)))
  out=add(out,term)
 return out
def coeff(p,powers):
 out={}
 for m,c in p.items():
  if all(m.count(v)==n for v,n in powers.items()):
   rest=tuple(v for v in m if v not in powers);out[rest]=out.get(rest,0)+c
 return {m:c for m,c in out.items() if c}
def degree(p,variables):return max((sum(v in variables for v in m) for m in p),default=-1)
def rec(p):return [[list(m),c] for m,c in sorted(p.items())]
def build(root):
 for n,h in PINS.items():need(sha((root/n).read_bytes())==h,'pin '+n)
 packet=read(root/'complete84_scaled_strong_output.json')['packet'];rows=packet['source'];by={r[0]:r for r in rows}
 need(len(rows)==len(by)==84,'full84 source')
 cuts={'tau_root':'T','wn2':'X','sn2':'Y','R10b':'k'}
 env={n:atom(v) for n,v in cuts.items()}
 def expand(v):
  if type(v)is int:return atom(v)
  if v not in env:
   _,op,a,b=by[v];a,b=expand(a),expand(b)
   env[v]=mul(a,b) if op=='*' else add(a,b,1 if op=='+' else -1)
  return env[v]
 expected_rows=[
 ['tau_square','*','tau_root','tau_root'],['UM','*','wn2','sn2'],['ksn2','*','R10b','sn2'],
 ['first_root_base','*','UM','ksn2'],['first_next','+','first_root_base','R10b'],
 ['first_product','*','first_root_base','first_next'],['norm_first','-','tau_square','first_product']]
 need(all(by[r[0]]==r for r in expected_rows),'literal dependent component')
 component=[r for r in expected_rows if r[0] not in ['UM','ksn2']]
 need(Counter(r[1] for r in component)=={'*':3,'+':1,'-':1},'five-gate ledger')
 T,X,Y,k=map(atom,['T','X','Y','k'])
 P=add(add(power(T,2),mul(mul(power(X,2),power(Y,4)),power(k,2)),-1),mul(mul(X,power(Y,2)),power(k,2)),-1)
 need(expand('norm_first')==P and expand('UM')==mul(X,Y) and expand('ksn2')==mul(k,Y),'full cut expansion')
 rad=add(mul(mul(power(X,2),power(Y,4)),power(k,2)),mul(mul(X,power(Y,2)),power(k,2)))
 need(min(m.count('X') for m in rad)==1,'odd X radicand valuation')
 # A nonzero two-by-two minor certifies support dimension at least two.
 points=[tuple(m.count(v) for v in ['T','X','Y','k']) for m in P]
 origin=points[0];vectors=[tuple(x-y for x,y in zip(p,origin)) for p in points[1:]]
 minors=[(i,j,vectors[0][i]*vectors[1][j]-vectors[0][j]*vectors[1][i]) for i in range(4) for j in range(i+1,4)]
 need(any(v for _,_,v in minors),'two-dimensional Newton support')
 # General two-product coefficient calculation, independently expanded.
 a,b,h,q,r,s,t0,uT,uX,uk,u0,vT,vX,vk,v0,bb,zT,zX,zk,z0=map(atom,
  ['alpha','beta','h','q0','r0','s0','t0','uT','uX','uk','u0','vT','vX','vk','v0','b0','zT','zX','zk','z0'])
 Q=add(add(add(mul(mul(q,X),k),mul(r,X)),mul(s,k)),t0)
 u=add(add(add(mul(uT,T),mul(uX,X)),mul(uk,k)),u0)
 v=add(add(add(mul(vT,T),mul(vX,X)),mul(vk,k)),v0)
 z=add(add(add(mul(zT,T),mul(zX,X)),mul(zk,k)),z0)
 F=add(add(mul(h,mul(add(mul(a,Q),u),add(mul(b,Q),v))),mul(bb,Q)),z)
 Ak=add(mul(a,s),uk);Bk=add(mul(b,s),vk)
 coef={
 'k2_at_X0':coeff(F,{'X':0,'T':0,'k':2}),
 'Tk_at_X0':coeff(F,{'X':0,'T':1,'k':1}),
 'T2_at_X0':coeff(F,{'X':0,'T':2,'k':0}),
 'Xk2':coeff(F,{'X':1,'T':0,'k':2})}
 need(coef['k2_at_X0']==mul(h,mul(Ak,Bk)),'k2 coefficient')
 need(coef['Tk_at_X0']==mul(h,add(mul(Ak,vT),mul(Bk,uT))),'Tk coefficient')
 need(coef['T2_at_X0']==mul(h,mul(uT,vT)),'T2 coefficient')
 need(coef['Xk2']==mul(mul(h,q),add(mul(a,Bk),mul(b,Ak))),'forbidden cubic coefficient')
 forced={'uk':mul(atom(-1),mul(a,s)),'vk':mul(atom(-1),mul(b,s))}
 need(not sub(coef['Xk2'],forced),'forced cubic vanishes')
 # Explicit examples only corroborate generic specialization; not a circuit search.
 examples=[atom(1),add(Y,atom(1),-1),mul(add(Y,atom(1),-1),add(Y,atom(2),-1)),
 add(power(Y,2),atom(1)),add(T,atom(1)),add(X,k),add(mul(T,X),Y),
 mul(add(Y,atom(1),-1),add(T,k)),add(mul(add(Y,atom(1),-1),power(T,3)),atom(1)),
 P,power(P,2),add(power(T,2),power(k,2))]
 samples=[]
 for G in examples:
  d=degree(G,{'T','X','k'});t=1
  while degree(sub(G,{'Y':atom(t)}),{'T','X','k'})!=d:t+=1
  Gt=sub(G,{'Y':atom(t)});Pt=sub(P,{'Y':atom(t)});target=mul(Gt,Pt)
  need(degree(target,{'T','X','k'})==d+4,'specialized product degree')
  need(coeff(Pt,{'X':1,'k':2,'T':0})==atom(-t*t),'nonzero cubic target')
  samples.append({'multiplier':rec(G),'t':t,'remaining_degree':d,'target_degree':d+4})
 return {'status':'PASS_FIRST_NORM_POLYNOMIAL_SCALING','source_sha256':sha(Path(__file__).read_bytes()),
  'dependencies':PINS,'full84_source_sha256':sha(canon(rows)),
  'literal_paid_producers_and_component':expected_rows,'paid_map':cuts,
  'component_ledger':{'M':3,'A':2,'total':5},'expanded_P':rec(P),'radicand_X_valuation':1,
  'Newton_support':points,'support_minors':minors,'general_two_product_coefficients':{n:rec(p) for n,p in coef.items()},
  'forced_Xk2_coefficient':[],'generic_specialization_examples':samples,
  'scope':{'all_nonzero_polynomial_multipliers':'proved in companion, not inferred from finite examples',
   'independent_variables':['T','X','Y','k'],'dependent_paid_ports':['E=XY','Z=kY'],
   'bound':'at least 3M and at least 2A separately','extra_paid_registers':False,
   'new_complete_circuit':False,'global84_minimum_claim':False,'predecessor_execution':False}}
def main():
 ap=argparse.ArgumentParser();ap.add_argument('--root',required=True,type=Path)
 g=ap.add_mutually_exclusive_group(required=True);g.add_argument('--output',type=Path);g.add_argument('--expect',type=Path)
 a=ap.parse_args();r=build(a.root)
 if a.output:
  with a.output.open('x') as f:f.write(json.dumps(r,sort_keys=True,indent=2)+'\n')
 else:need(canon(r)==canon(read(a.expect)),'exact typed receipt')
 print(r['status'])
if __name__=='__main__':main()
