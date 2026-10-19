#!/usr/bin/env python3
"""Check an actual K/S/MP/GEN derivation of atomic DNE from weak vacuity.

Formula metavariable p and binder i are schematic. F may be ANY fixed formula,
including the native alias Rel(0,0). GEN is applied only to closed derivations.
Weak vacuity is the sole extra premise; a second certificate derives it from
the actual negative-conjunction bundle, without extracting ordinary conjuncts.
The checker is proof-local, independent of a truth-value model.
"""
if not __debug__:
 raise RuntimeError('This proof checker must run with Python assertions enabled.')

from dataclasses import dataclass
from functools import cache
from pathlib import Path
import json

F=('rel',0,0)
p=('meta','p')
i='i'
I=lambda a,b:('imp',a,b)
Q=lambda i,a:('all',i,a)
E=lambda i,a:I(Q(i,I(a,F)),F)
N=lambda a:I(a,F)
J=lambda a:N(N(a))
And=lambda a,b:N(I(a,N(b)))
@dataclass(frozen=True,eq=False)
class P:
 rule:str
 form:tuple
 args:tuple=()

def k(a,b):return P('K',I(a,I(b,a)))
def s(a,b,c):return P('S',I(I(a,I(b,c)),I(I(a,b),I(a,c))))
def mp(a,b):
 assert a.form[0]=='imp' and a.form[1]==b.form
 return P('MP',a.form[2],(a,b))
def hyp(a):return P('HYP',a)
def ax(name,a):return P(name,a)
def ident(a):return mp(mp(s(a,I(a,a),a),k(a,I(a,a))),k(a,a))
@cache
def abstract(a,t):
 if a not in assumptions(t):return mp(k(t.form,a),t)
 if t.rule=='HYP' and t.form==a:return ident(a)
 if t.rule=='MP':return mp(mp(s(a,t.args[1].form,t.form),abstract(a,t.args[0])),abstract(a,t.args[1]))
 return mp(k(t.form,a),t)
def gen(v,t):
 assert not assumptions(t)
 return P('GEN',Q(v,t.form),(v,t))
@cache
def assumptions(t):
 if t.rule=='HYP':return frozenset((t.form,))
 if t.rule=='MP':return assumptions(t.args[0])|assumptions(t.args[1])
 if t.rule=='GEN':return assumptions(t.args[1])
 return frozenset()
def rho2(v,a,b):return ax('rho2',I(Q(v,I(a,b)),I(Q(v,a),Q(v,b))))
def rho6(v,a):return ax('rho6',I(E(v,Q(v,a)),a))
def rho1(v,w):return ax('rho1',E(v,('eq',v,w)))
def mono(v,t):
 a,b=t.form[1:]
 return mp(rho2(v,a,b),gen(v,t))
def compose(t,u):
 a,b=t.form[1:];assert u.form[1]==b
 return abstract(a,mp(u,mp(t,hyp(a))))
def efq(b):
 r=rho6(i,b);x=r.form[1][1]
 return abstract(F,mp(r,mp(k(F,x),hyp(F))))
def qf_bottom(v):
 e=('eq',v,'j')
 return compose(mono(v,k(F,e)),rho1(v,'j'))

def weak_from_double_vacuity():
 v=I(p,Q(i,p));w=J(v)
 # Given p and not Qp, v would imply Qp, contradicting not Qp.
 nv=abstract(v,mp(hyp(N(Q(i,p))),mp(hyp(v),hyp(p))))
 contradiction=mp(hyp(w),nv)
 result=abstract(w,abstract(p,abstract(N(Q(i,p)),contradiction)))
 assert result.form==I(J(v),I(p,J(Q(i,p))))
 return result

def bundle_component_dn(component):
 # The actual bundle is ((C & G) & (vr & ve)).
 c=('meta','C');g=('meta','G');ve=('meta','ve');vr=I(p,Q(i,p))
 bundle=And(And(c,g),And(vr,ve))
 def right_dn(a,b):
  # (a & b) -> jj b, entirely intuitionistic.
  h=And(a,b)
  nab=abstract(a,hyp(N(b)))
  return abstract(h,abstract(N(b),mp(hyp(h),nab)))
 def left_dn(a,b):
  h=And(a,b)
  # Under not a, a -> not b follows by explosion.
  nb=abstract(b,mp(hyp(N(a)),hyp(a)))
  nab=abstract(a,nb)
  return abstract(h,abstract(N(a),mp(hyp(h),nab)))
 def jmono(t):
  a,b=t.form[1:]
  na=abstract(a,mp(hyp(N(b)),mp(t,hyp(a))))
  return abstract(J(a),abstract(N(b),mp(hyp(J(a)),na)))
 def flatten(a):
  # jjjj a -> jj a
  na=N(a)
  nja=abstract(J(a),mp(hyp(J(a)),hyp(na)))
  return abstract(J(J(a)),abstract(na,mp(hyp(J(J(a))),nja)))
 r=right_dn(And(c,g),And(vr,ve))
 l=jmono(left_dn(vr,ve))
 result=compose(compose(r,l),flatten(vr))
 assert result.form==I(bundle,J(vr))
 return result

def atomic_dne():
 w=I(p,J(Q(i,p)))
 # The only additional axiom is weak atomic vacuity.
 wp=ax('weak_vacuity',w)
 # p -> (not Qp -> F) is definitionally the same theorem.
 generalized=gen(i,wp)
 t1=mp(rho2(i,p,I(N(Q(i,p)),F)),generalized)
 qnp=Q(i,N(Q(i,p)))
 qp=Q(i,p)
 qnf=Q(i,I(N(qp),F))
 # Under Q not Qp and Qp obtain QF, hence F.
 q_to_qnf=mp(t1,hyp(qp))
 q_to_f=mp(qf_bottom(i),mp(mp(rho2(i,N(qp),F),q_to_qnf),hyp(qnp)))
 qnp_to_nqp=abstract(qnp,abstract(qp,q_to_f))
 # Under Q not Qp and p, use weak vacuity and not Qp to obtain F.
 qnp_to_np=abstract(qnp,abstract(p,mp(mp(wp,hyp(p)),mp(qnp_to_nqp,hyp(qnp)))))
 # jj p refutes Q not Qp; rho6 then concludes p.
 nqnp=abstract(qnp,mp(hyp(J(p)),mp(qnp_to_np,hyp(qnp))))
 result=abstract(J(p),mp(rho6(i,p),nqnp))
 assert result.form==I(J(p),p)
 return result

def classical_rho8():
 a=('meta','a');b=('meta','b');c=p;u=('meta','u')
 h1=I(I(c,u),a);h2=I(a,c)
 c_to_u=abstract(c,mp(efq(u),mp(hyp(N(c)),hyp(c))))
 cc=mp(hyp(h2),mp(hyp(h1),c_to_u))
 nnc=abstract(N(c),mp(hyp(N(c)),cc))
 result=abstract(h1,abstract(h2,abstract(b,mp(atomic_dne(),nnc))))
 assert result.form==I(I(I(c,u),a),I(I(a,c),I(b,c)))
 return result

def check(t,seen):
 if t in seen:return
 seen.add(t)
 r=t.rule;f=t.form
 if r=='K':a=f[1];assert f==I(a,I(f[2][1],a))
 elif r=='S':
  a=f[1][1];b=f[1][2][1];c=f[1][2][2]
  assert f==I(I(a,I(b,c)),I(I(a,b),I(a,c)))
 elif r=='MP':
  x,y=t.args;assert x.form==I(y.form,f);check(x,seen);check(y,seen)
 elif r=='GEN':
  v,x=t.args;assert f==Q(v,x.form) and not assumptions(x);check(x,seen)
 elif r=='rho2':
  v=f[1][1];a=f[1][2][1];b=f[1][2][2]
  assert f==I(Q(v,I(a,b)),I(Q(v,a),Q(v,b)))
 elif r=='rho6':
  a=f[2];v=f[1][1][1];assert f==I(E(v,Q(v,a)),a)
 elif r=='rho1':
  v=f[1][1];e=f[1][2][1];assert e[0]=='eq' and e[1]==v and f==E(v,e)
 elif r=='weak_vacuity':assert f==I(p,J(Q(i,p)))
 elif r=='HYP':pass
 else:raise AssertionError(r)

def export_proof(roots):
 # A compact replay artifact: formulas and proofs are separately interned.
 forms=[];fi={};nodes=[];ni={}
 def formula(f):
  if f in fi:return fi[f]
  k=len(forms);fi[f]=k;forms.append(f);return k
 def proof(t):
  if t in ni:return ni[t]
  if t.rule=='MP':args=[proof(x)for x in t.args]
  elif t.rule=='GEN':args=[t.args[0],proof(t.args[1])]
  else:args=[]
  k=len(nodes);ni[t]=k;nodes.append(dict(rule=t.rule,formula=formula(t.form),args=args));return k
 roots={name:proof(t)for name,t in roots.items()}
 return dict(formulas=forms,proof_nodes=nodes,roots=roots)

def main():
 report={};roots={}
 for name,fn in [('weak_from_double_vacuity',weak_from_double_vacuity),('bundle_component_dn',lambda:bundle_component_dn('vr')),('atomic_dne',atomic_dne),('classical_rho8',classical_rho8)]:
  proof=fn();roots[name]=proof;assert not assumptions(proof)
  seen=set();check(proof,seen)
  counts={}
  for t in seen:counts[t.rule]=counts.get(t.rule,0)+1
  report[name]=dict(distinct_proof_nodes=len(seen),rules=counts,formula=repr(proof.form))
 report['scope']='Schematic Hilbert K/S/MP/GEN proof. F is literally Rel(0,0); no closed-bottom or alpha-renaming premise. Weak atomic vacuity derived from actual source bundle as a separate implication certificate. No full consistency bridge.'
 Path(__file__).with_name('hilbert_proofs.json').write_text(json.dumps(export_proof(roots),separators=(',',':'))+'\n')
 Path(__file__).with_name('hilbert_atomic_stability_results.json').write_text(json.dumps(report,indent=2)+'\n')
 print(json.dumps(report,indent=2))
if __name__=='__main__':main()
