#!/usr/bin/env python3
"""Independent exact-algebra check of the six-port first-norm lower-bound proof.

Uses SymPy rather than the author's sparse-polynomial implementation. The
classification of arbitrary straight-line programs is proved in the note;
this executable checks its exact algebra and literal source attainment.
"""
import argparse,hashlib,json
from pathlib import Path
import sympy as sp
if not __debug__:raise RuntimeError('Run without -O')
AUTHOR_PINS={'py':'2eecbcfa6d48872f8522cdb839517232a2208cfc9f9466f5780c3d0584ddb077','json':'e66759e01ae27cb41abe419a3875180c68467363c3c249943bbc8c589552fee4','md':'3f7580635b63b6cc7bda27b23022db99c85fdc4341c34ea1fb5d55f42e00c2fc'}
PARENT_PINS={'complete86_factored_first_root.py':'29cf4100b846bcbabb05185550b7d9ead6b572746048b94998a13c83eeaff40f','complete86_factored_first_root.json':'2dfe46fe9c5537ff51eb3c542806c58242238363e6018f9daab7eabf0b6fe61e','complete86_factored_first_root.md':'9f2b50449e0724e523e9dd5d022f229b77504976f23ee52ca2917cf11ceb322b'}
def need(p,m):
 if not p:raise ValueError(m)
def sha(raw):return hashlib.sha256(raw).hexdigest()
def exact(a,b):
 if type(a)is not type(b):return False
 if type(a)is dict:return a.keys()==b.keys() and all(exact(a[k],b[k]) for k in a)
 if type(a)is list:return len(a)==len(b) and all(exact(x,y) for x,y in zip(a,b))
 return a==b

def verify(root,author):
 root=Path(root);author=Path(author)
 for ext,pin in AUTHOR_PINS.items():need(sha(author.with_suffix('.'+ext).read_bytes())==pin,'Frozen author '+ext)
 for n,pin in PARENT_PINS.items():need(sha((root/n).read_bytes())==pin,'Actual parent '+n)
 # No author/helper module is imported or executed.
 old=json.loads((root/'complete86_factored_first_root.json').read_text());saved=json.loads(author.with_suffix('.json').read_text())
 T,X,Y,k=sp.symbols('T X Y k');E=X*Y;Z=k*Y;P=T**2-X**2*Y**4*k**2-X*Y**2*k**2
 need(sp.expand(P-(T*T-(E*Z)*(E*Z+k)))==0,'Actual dependent-port target')
 block_names=['tau_square','first_root_base','first_next','first_product','norm_first'];blocks=[]
 for form in old['forms']:
  d={n:(op,a,b) for n,op,a,b in form['source']}
  need(d['UM']==('*','wn2','sn2') and d['ksn2']==('*','R10b','sn2'),'Both actual producer cones')
  selected=[row for row in form['source'] if row[0] in block_names]
  need([row[0] for row in selected]==block_names,'All five actual source gates')
  env={'tau_root':T,'UM':E,'ksn2':Z,'R10b':k};cost={'M':0,'A':0}
  for n,op,a,b in selected:
   env[n]=sp.expand(env[a]*env[b] if op=='*' else env[a]+env[b] if op=='+' else env[a]-env[b]);cost['M' if op=='*' else 'A']+=1
  need(env['norm_first']==P and cost=={'M':3,'A':2},'Full literal component attainment')
  live={'norm_first'}
  for n,op,a,b in reversed(selected):need(n in live,'Every counted component gate live');live.update((a,b))
  blocks.append({'normalized':form['normalized'],'source':selected,'M':3,'A':2})
 R=sp.expand(P.subs(Y,1));need(R==T*T-X*X*k*k-X*k*k,'Specialization with no nonlinear free ports')
 # Independent general two-product normal form; no affine constraints on Q's
 # lower coefficients are imposed, which makes the hypothetical family larger.
 c,r,s,t,aa,bb,h,z=sp.symbols('c r s t aa bb h z')
 uT,uX,uk,u0,vT,vX,vk,v0,zT,zX,zk,z0=sp.symbols('uT uX uk u0 vT vX vk v0 zT zX zk z0')
 Q=c*X*k+r*X+s*k+t
 U=aa*Q+uT*T+uX*X+uk*k+u0;V=bb*Q+vT*T+vX*X+vk*k+v0
 Out=sp.Poly(sp.expand(h*U*V+z*Q+zT*T+zX*X+zk*k+z0),T,X,k)
 A=aa*s+uk;B=bb*s+vk
 coefficient=lambda powers:sp.expand(Out.coeff_monomial(powers))
 need(sp.expand(coefficient(k**2)-h*A*B)==0,'Full restricted k² coefficient')
 need(sp.expand(coefficient(T*k)-h*(uT*B+vT*A))==0,'Full restricted Tk coefficient')
 need(coefficient(T*T)==h*uT*vT,'Nonzero T² coefficient')
 cubic=coefficient(X*k*k);need(sp.expand(cubic-h*c*(aa*B+bb*A))==0,'Full Xk² coefficient, including both cross terms')
 # Normalize the nonzero T coefficients. A quadratic T² product can have no
 # k coefficient in either linear factor over Q: a+b=0 and ab=0 give a²=0.
 a,b=sp.symbols('a b');quad=sp.Poly((T+a*k)*(T+b*k),T,k)
 need(quad.coeff_monomial(T*k)==a+b and quad.coeff_monomial(k*k)==a*b,'Normalized quadratic coefficient equations')
 need(sp.expand(quad.as_expr().subs(b,-a)-T*T)==-a*a*k*k,'Field square obstruction after the forced sum relation')
 forced=sp.expand(Out.as_expr().subs({uk:-aa*s,vk:-bb*s}))
 need(sp.Poly(forced,T,X,k).coeff_monomial(X*k*k)==0 and sp.Poly(R,T,X,k).coeff_monomial(X*k*k)==-1,'Forced zero versus required cubic')
 # Independent exact factorization backs up the general odd-valuation proof.
 radicand=(k*Y)**2*X*(X*Y*Y+1)
 need(sp.expand(T*T-radicand)==P,'Monic quadratic radicand')
 valuation=min(m[0] for m,c0 in sp.Poly(radicand,X,Y,k).terms())
 need(valuation==1 and sp.expand((radicand/X).subs(X,0))==k*k*Y*Y,'Exact odd X valuation')
 unit,factors=sp.factor_list(P,T,X,Y,k)
 need(unit==1 and len(factors)==1 and factors[0][1]==1 and sp.expand(factors[0][0]-P)==0,'Independent rational polynomial irreducibility check')
 monomials=sp.Poly(P,T,X,Y,k).monoms();need(len(monomials)==3 and all(min(m[i] for m in monomials)==0 for i in range(4)),'Three terms, no nonunit monomial factor')
 need(saved['lower_bounds']=={'multiplications':3,'additions_subtractions':2,'total':5},'Reviewed exact model result')
 return {'status':'PASS_INDEPENDENT_FIRST_NORM_FIVE_GATE_BOUND','review_source_sha256':sha(Path(__file__).read_bytes()),'author_pins':AUTHOR_PINS,'parent_pins':PARENT_PINS,
  'attainment':blocks,'symbolic_checks':{'complete_source_attainments':2,'two_product_coefficients':4,'normalized_quadratic_constraint':True,'forced_cubic':0,'required_cubic':-1,'radicand_X_valuation':valuation,'rational_irreducible_factors':1,'target_terms':3},
  'lower_bounds':{'M':3,'A':2,'total':5},
  'scope':'Exact division-free polynomial evaluation over Q at T,X,Y,k,E=XY,Z=kY only. Every multiplication/addition counted; each lower bound relaxes the other count. Not a lower bound for the full universal circuit, additional paid ports, changed coordinates, divisions by variable expressions or merely equivalent zero sets. The unrestricted SLP classification and valuation argument are mathematical proofs, not finite circuit enumeration.'}
def main():
 p=argparse.ArgumentParser();p.add_argument('--root',type=Path,required=True);p.add_argument('--author',type=Path,default=Path(__file__).with_name('first_norm_five_gate_lower_bound.py'));p.add_argument('--output',type=Path);p.add_argument('--expect',type=Path);a=p.parse_args();r=verify(a.root,a.author);raw=json.dumps(r,indent=2,sort_keys=True)+'\n'
 if a.output:a.output.write_text(raw)
 if a.expect:need(exact(json.loads(raw),json.loads(a.expect.read_text())),'Fresh exact saved independent receipt')
 print(json.dumps({'status':r['status'],'lower_bounds':r['lower_bounds'],'symbolic_checks':r['symbolic_checks']},sort_keys=True))
if __name__=='__main__':main()
