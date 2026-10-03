#!/usr/bin/env python3
"""Sharp exact first-norm component bound at its actual dependent paid ports."""
import argparse,hashlib,json
from pathlib import Path
PINS={'complete86_factored_first_root.py':'29cf4100b846bcbabb05185550b7d9ead6b572746048b94998a13c83eeaff40f',
'complete86_factored_first_root.json':'2dfe46fe9c5537ff51eb3c542806c58242238363e6018f9daab7eabf0b6fe61e',
'complete86_factored_first_root.md':'9f2b50449e0724e523e9dd5d022f229b77504976f23ee52ca2917cf11ceb322b'}
def need(x,m):
 if not x:raise ValueError(m)
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def exact(a,b):
 if type(a)is not type(b):return False
 if type(a)is dict:return a.keys()==b.keys() and all(exact(a[k],b[k]) for k in a)
 if type(a)is list:return len(a)==len(b) and all(exact(x,y) for x,y in zip(a,b))
 return a==b
def const(n):return {():n} if n else {}
def var(n):return {(n,):1}
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
def sub(a,b):return add(a,b,-1)
def square(a):return mul(a,a)
def sum_poly(*terms):
 d={}
 for t in terms:d=add(d,t)
 return d
def subst(p,values):
 d={}
 for m,c in p.items():
  t=const(c)
  for n in m:t=mul(t,values.get(n,var(n)))
  d=add(d,t)
 return d
def coef(p,powers,variables=('X','k','T')):
 d={}
 for m,c in p.items():
  if all(m.count(n)==powers.get(n,0) for n in variables):
   k=tuple(n for n in m if n not in variables);d[k]=d.get(k,0)+c
 return {m:c for m,c in d.items() if c}
def record(p):return [{'monomial':list(m),'coefficient':c} for m,c in sorted(p.items())]
def verify(root):
 root=Path(root)
 for n,h in PINS.items():need(sha(root/n)==h,'actual parent pin '+n)
 j=json.loads((root/'complete86_factored_first_root.json').read_text())
 T,X,Y,k=[var(n) for n in ('T','X','Y','k')];E=mul(X,Y);Z=mul(k,Y);L=mul(E,Z)
 P=sub(square(T),mul(L,add(L,k)))
 need(P=={('T','T'):1,('X','X','Y','Y','Y','Y','k','k'):-1,('X','Y','Y','k','k'):-1},'literal three-term target')
 block=[['tau_square','*','tau_root','tau_root'],['first_root_base','*','UM','ksn2'],['first_next','+','first_root_base','R10b'],['first_product','*','first_root_base','first_next'],['norm_first','-','tau_square','first_product']]
 sources=[]
 for form in j['forms']:
  d={n:[op,a,b] for n,op,a,b in form['source']}
  need(d['UM']==['*','wn2','sn2'] and d['ksn2']==['*','R10b','sn2'],'actual E=XY and Z=kY producer definitions')
  selected=[r for r in form['source'] if r[0] in {r[0] for r in block}]
  need(exact(selected,block),'complete literal five-gate component')
  e={'tau_root':T,'UM':E,'ksn2':Z,'R10b':k};m=a=0
  for n,op,l,r in block:
   e[n]=mul(e[l],e[r]) if op=='*' else add(e[l],e[r],1 if op=='+' else -1)
   m+=op=='*';a+=op!='*'
  need(e['norm_first']==P and (m,a)==(3,2),'actual paid attainment')
  needed={'norm_first'}
  for n,op,l,r in reversed(block):need(n in needed,'all block gates live');needed.update((l,r))
  sources.append({'normalized':form['normalized'],'block':block,'M':m,'A':a,'operations':m+a})
 restricted=subst(P,{'Y':const(1)})
 need(restricted==sub(sub(square(T),mul(square(X),square(k))),mul(X,square(k))),'Y=1 restriction with only T,X,k free')
 top={m:c for m,c in restricted.items() if len(m)==4}
 need(top==mul(const(-1),square(mul(X,k))),'quartic square forces first-product quadratic direction')
 # General first product after the forced leading directions. Allowing independent
 # q,r,s,t only relaxes its affine-factor restrictions, strengthening the obstruction.
 q,r,s,t,alpha,beta,h,ux,uk,ut,u0,vx,vk,vt,v0,b,zx,zk,zt,z0=[var(n) for n in ['q','r','s','t','alpha','beta','h','ux','uk','ut','u0','vx','vk','vt','v0','b','zx','zk','zt','z0']]
 Q=sum_poly(mul(q,mul(X,k)),mul(r,X),mul(s,k),t)
 F=sum_poly(mul(alpha,Q),mul(ux,X),mul(uk,k),mul(ut,T),u0)
 G=sum_poly(mul(beta,Q),mul(vx,X),mul(vk,k),mul(vt,T),v0)
 output=sum_poly(mul(h,mul(F,G)),mul(b,Q),mul(zx,X),mul(zk,k),mul(zt,T),z0)
 A=add(mul(alpha,s),uk);B=add(mul(beta,s),vk)
 need(coef(output,{'k':2})==mul(h,mul(A,B)),'quadratic k² at X=0')
 need(coef(output,{'k':1,'T':1})==mul(h,add(mul(A,vt),mul(B,ut))),'quadratic Tk at X=0')
 need(coef(output,{'T':2})==mul(h,mul(ut,vt)),'nonzero quadratic T² at X=0')
 cubic=coef(output,{'X':1,'k':2})
 need(cubic==mul(h,mul(q,add(mul(alpha,B),mul(beta,A)))),'full cubic coefficient')
 canceled=subst(output,{'uk':mul(const(-1),mul(alpha,s)),'vk':mul(const(-1),mul(beta,s))})
 need(coef(canceled,{'X':1,'k':2})=={} and coef(restricted,{'X':1,'k':2})==const(-1),'forced zero versus actual nonzero cubic obstruction')
 # Irreducibility: the quadratic-in-T radicand has X-valuation exactly one.
 radicand=mul(square(mul(k,Y)),mul(X,add(mul(X,square(Y)),const(1))))
 need(P==sub(square(T),radicand),'monic quadratic in T')
 valuation=min(m.count('X') for m in radicand)
 need(valuation==1 and subst(add(mul(X,square(Y)),const(1)),{'X':const(0)})==const(1),'odd X-valuation; residual factor not divisible by X')
 need(len(P)==3 and all(min(m.count(n) for m in P)==0 for n in ('T','X','Y','k')),'three terms with no monomial factor')
 return {'status':'PASS_SHARP_DEPENDENT_PORT_FIRST_NORM_BOUND','source_sha256':sha(Path(__file__)),'parent_pins':PINS,
 'ports':{'independent':['T','X','Y','k'],'additional_paid_monomials':{'E':'X*Y','Z':'k*Y'}},
 'target':record(P),'attainment':sources,'lower_bounds':{'multiplications':3,'additions_subtractions':2,'total':5},
 'restricted_target':record(restricted),'restricted_quartic':record(top),'two_product_cubic_coefficient':record(cubic),
 'forced_cubic_coefficient':[],'required_cubic_coefficient':-1,'radicand_X_valuation':valuation,
 'proof_scope':'Exact division-free evaluation with fixed rational constants at these six paid ports only. Each lower bound allows arbitrarily many operations of the other kind. No bound on other paid registers, full universal circuits, changed coordinates or merely equivalent zero sets.'}
def main():
 p=argparse.ArgumentParser();p.add_argument('--root',type=Path,default=Path(__file__).resolve().parent);p.add_argument('--output',type=Path);p.add_argument('--expect',type=Path);v=p.parse_args();j=verify(v.root)
 if v.expect:need(exact(j,json.loads(v.expect.read_text())),'exact saved receipt')
 if v.output:v.output.write_text(json.dumps(j,indent=2,sort_keys=True)+'\n')
 print(json.dumps({'status':j['status'],'lower_bounds':j['lower_bounds']}))
if __name__=='__main__':main()
