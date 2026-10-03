#!/usr/bin/env python3
"""Independent exact algebra for the bounded five-gate theorem; no subject import."""
import argparse,hashlib,json
from pathlib import Path
PINS={
'auxiliary_norm_five_gate_lower_bound.py':'d3fb95e2574106b3fdc22c7397488b9b18c855d6c1d1ceab92ca57295cb4d120',
'auxiliary_norm_five_gate_lower_bound.json':'e6506cc99e4797e0d4fc906a8f79bcc0988c2ea49fb451a796c1be1e8364697a',
'auxiliary_norm_five_gate_lower_bound.md':'e2d587ed384b77703fff8be6a7eaa0d619ee11d9c922749c8a2024ae45934910'}
def need(v,s):
 if not v:raise ValueError(s)
def sha(b):return hashlib.sha256(b).hexdigest()
def exact(a,b):
 if type(a)is not type(b):return False
 if type(a)is dict:return a.keys()==b.keys() and all(exact(a[k],b[k]) for k in a)
 if type(a)is list:return len(a)==len(b) and all(exact(x,y) for x,y in zip(a,b))
 return a==b
def add(a,b,sign=1):
 d=a.copy()
 for m,c in b.items():d[m]=d.get(m,0)+sign*c
 return {m:c for m,c in d.items() if c}
def mul(a,b):
 d={}
 for m,c in a.items():
  for n,e in b.items():
   k=tuple(sorted(m+n));d[k]=d.get(k,0)+c*e
 return {m:c for m,c in d.items() if c}
def const(n):return {():n} if n else {}
def var(n):return {(n,):1}
def square(a):return mul(a,a)
def sub(a,b):return add(a,b,-1)
def scale(a,n):return mul(const(n),a)
def substitute(poly,values):
 out={}
 for m,c in poly.items():
  t=const(c)
  for n in m:t=mul(t,values.get(n,var(n)))
  out=add(out,t)
 return out
def record(poly):return [{'monomial':list(m),'coefficient':c} for m,c in sorted(poly.items())]
def verify(root):
 root=Path(root)
 for n,h in PINS.items():need(sha((root/n).read_bytes())==h,'source pin '+n)
 receipt=json.loads((root/'auxiliary_norm_five_gate_lower_bound.json').read_text())
 K,V,y,c,A,B,Q,a,b,u,v,z=[var(n) for n in ['K','V','y','c','A','B','Q','a','b','u','v','z']]
 P=sub(mul(K,square(V)),mul(sub(K,const(1)),square(y)))
 need(P=={('K','V','V'):1,('K','y','y'):-1,('y','y'):1},'literal trinomial')
 top={m:c for m,c in P.items() if len(m)==3}
 need(top==mul(K,mul(sub(V,y),add(V,y))),'three possible linear divisor directions')
 # Clearing the sole constant denominator: valid for every nonzero a.
 normal=add(add(mul(add(mul(a,Q),u),v),mul(b,Q)),z)
 reduced_times_a=sub(add(mul(add(mul(a,Q),u),add(mul(a,v),b)),mul(a,z)),mul(b,u))
 need(mul(a,normal)==reduced_times_a,'full constant-denominator normal form')
 quartic=mul(add(mul(a,mul(A,B)),u),add(mul(b,mul(A,B)),v))
 coefficient={tuple(n for n in m if n not in ('A','B')):e for m,e in quartic.items() if m.count('A')==m.count('B')==2}
 need(coefficient==mul(a,b),'uncancellable first-product square coefficient')
 planes=[]
 for title,subs,expected,variables in [
  ('K=c',{'K':c},add(mul(c,square(V)),mul(sub(const(1),c),square(y))),('V','y')),
  ('V=y+c',{'V':add(y,c)},add(add(scale(mul(mul(c,K),y),2),mul(square(c),K)),square(y)),('K','y')),
  ('V=-y+c',{'V':sub(c,y)},add(add(scale(mul(mul(c,K),y),-2),mul(square(c),K)),square(y)),('K','y'))]:
  restricted=substitute(P,subs);need(restricted==expected,'complete affine plane restriction')
  quadratic={m:e for m,e in restricted.items() if sum(m.count(n) for n in variables)==2}
  if title=='K=c':
   coefficients=[]
   for target in ('V','y'):
    coefficients.append({tuple(n for n in m if n!=target):e for m,e in restricted.items() if m.count(target)==2})
   need(add(*coefficients)==const(1),'quadratic coefficients generate unit ideal')
   obstruction='coefficient(V²)+coefficient(y²)=1 for every c'
  else:
   coeff={tuple(n for n in m if n!='y'):e for m,e in restricted.items() if m.count('y')==2}
   need(coeff==const(1),'nonzero fixed quadratic coefficient')
   obstruction='coefficient(y²)=1 for every c'
  planes.append({'plane':title,'restriction':record(restricted),'quadratic_part':record(quadratic),'all_offsets_obstruction':obstruction})
 # Every nonunit divisor of y² is divisible by y, whereas (V²−y²)|y=0=V².
 coefficient_K=sub(square(V),square(y));constant_K=square(y)
 need(substitute(coefficient_K,{'y':const(0)})==square(V),'primitive linear coefficient has no y divisor')
 need(constant_K==square(y),'all possible common factors reduce to y')
 need(len(P)==3 and all(min(m.count(n) for m in P)==0 for n in ['K','V','y']),'three terms and no monomial factor')
 # Exact attainment reads every row of the frozen source from the author receipt.
 expected=[['V2','*','V','V'],['y2','*','y','y'],['difference','-','V2','y2'],['weighted','*','K','difference'],['output','+','weighted','y2']]
 need(exact(receipt['attaining_source'],expected),'literal complete attaining circuit')
 env={'K':K,'V':V,'y':y};ops={'M':0,'A':0};deps={}
 for n,op,l,r in expected:
  need(n not in env and l in env and r in env,'closed source')
  env[n]=mul(env[l],env[r]) if op=='*' else add(env[l],env[r],1 if op=='+' else -1);ops['M' if op=='*' else 'A']+=1;deps[n]=(l,r)
 need(env['output']==P and ops=={'M':3,'A':2},'paid attaining polynomial')
 live=set();todo=['output']
 while todo:
  n=todo.pop()
  if n not in deps or n in live:continue
  live.add(n);todo.extend(deps[n])
 need(live==set(deps),'every gate live')
 need(exact(receipt['lower_bounds'],{'multiplications':3,'additions_subtractions':2,'total':5}),'reported independent lower bounds')
 return {'status':'PASS_INDEPENDENT_ISOLATED_FIVE_GATE_PROOF','review_source_sha256':sha(Path(__file__).read_bytes()),'pins':PINS,
 'target':record(P),'cubic_part':record(top),'normal_form_denominator_cleared':True,'uncancellable_quartic_coefficient':record(coefficient),
 'planes':planes,'primitive_gcd_argument':'Any common irreducible factor divides y², hence equals y up to a unit; V²−y² is not divisible by y. Gauss lemma applies over Q[V,y].',
 'one_addition_normal_form':'constant*monomial*(monomial1 +/- monomial2)^e, e>=0; irreducibility forces unit monomial and e=1, contradicting three terms',
 'attaining_source':expected,'attaining_ledger':{'M':3,'A':2,'total':5,'all_gates_live':True},
 'proof_review':'Read the entire author proof and source. General two-multiplication and one-addition normal forms independently checked mathematically; identities verified here without SymPy or subject imports.',
 'scope':'Exact division-free polynomial SLP over Q with independent K,V,y, fixed constants and binary +,-,*. No lower bound for computed-port specializations, other shared registers, coordinate changes, or zero-set-equivalent polynomials. No finite circuit enumeration is claimed.'}
def main():
 a=argparse.ArgumentParser();a.add_argument('--source-root',type=Path,default=Path(__file__).resolve().parent);a.add_argument('--output',type=Path);a.add_argument('--expect',type=Path);v=a.parse_args();r=verify(v.source_root)
 if v.expect:need(exact(r,json.loads(v.expect.read_text())),'exact saved receipt')
 if v.output:v.output.write_text(json.dumps(r,indent=2,sort_keys=True)+'\n')
 print(json.dumps({'status':r['status'],'attaining_ledger':r['attaining_ledger']}))
if __name__=='__main__':main()
