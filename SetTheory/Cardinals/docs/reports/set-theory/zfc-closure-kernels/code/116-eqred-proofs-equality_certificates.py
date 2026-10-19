#!/usr/bin/env python3
"""Finite K/S/MP/GEN certificates for equality reflexivity, symmetry, transitivity.

The sole added axiom is canonical V on Eq(x,x), with its binder represented
by the explicit symbolic native-code term ('weq','x','x'). No DNE, old vacuity,
CP, GIC, alpha conversion, or generalization under assumptions is used.
"""
from dataclasses import dataclass
from functools import cache
from pathlib import Path
import json
F=('rel',0,0)
I=lambda a,b:('imp',a,b)
Q=lambda i,a:('all',i,a)
N=lambda a:I(a,F)
Ex=lambda i,a:N(Q(i,N(a)))
Eq=lambda a,b:('eq',a,b)
@dataclass(frozen=True,eq=False)
class P:
 rule:str
 form:tuple
 args:tuple=()
def k(a,b):return P('K',I(a,I(b,a)))
def s(a,b,c):return P('S',I(I(a,I(b,c)),I(I(a,b),I(a,c))))
def hyp(a):return P('HYP',a)
def mp(t,u):
 if t.form!=I(u.form,t.form[2]):raise ValueError('MP')
 return P('MP',t.form[2],(t,u))
@cache
def assumptions(t):
 if t.rule=='HYP':return frozenset((t.form,))
 if t.rule=='MP':return assumptions(t.args[0])|assumptions(t.args[1])
 if t.rule=='GEN':return assumptions(t.args[1])
 return frozenset()
def ident(a):return mp(mp(s(a,I(a,a),a),k(a,I(a,a))),k(a,a))
@cache
def abst(a,t):
 if a not in assumptions(t):return mp(k(t.form,a),t)
 if t.rule=='HYP' and t.form==a:return ident(a)
 if t.rule=='MP':return mp(mp(s(a,t.args[1].form,t.form),abst(a,t.args[0])),abst(a,t.args[1]))
 raise ValueError('bad abstraction')
def gen(i,t):
 if assumptions(t):raise ValueError('GEN with hypotheses')
 return P('GEN',Q(i,t.form),(i,t))
def rho1(i,j):return P('rho1',Ex(i,Eq(i,j)))
def rho2(i,a,b):return P('rho2',I(Q(i,I(a,b)),I(Q(i,a),Q(i,b))))
def rho6(i,a):return P('rho6',I(Ex(i,Q(i,a)),a))
def rho7(a,b,c):return P('rho7',I(Eq(c,a),I(Eq(c,b),Eq(a,b))))
def canon_eq(a,b):
 e=Eq(a,b);i=('weq',a,b)
 return P('V_eq',I(e,Q(i,e)))
def mono(i,t):
 a,b=t.form[1:];return mp(rho2(i,a,b),gen(i,t))
def contra(t):
 a,b=t.form[1:]
 return abst(N(b),abst(a,mp(hyp(N(b)),mp(t,hyp(a)))))
def emono(i,t):return contra(mono(i,contra(t)))
def refl(x):
 e=Eq(x,x);z=('weq',x,x);d=Eq(z,x)
 d_to_e=abst(d,mp(mp(rho7(x,x,z),hyp(d)),hyp(d)))
 ex_e=mp(emono(z,d_to_e),rho1(z,x))
 ex_qe=mp(emono(z,canon_eq(x,x)),ex_e)
 return mp(rho6(z,e),ex_qe)
def sym(x,y):
 d=Eq(x,y)
 return abst(d,mp(mp(rho7(y,x,x),hyp(d)),refl(x)))
def trans(x,y,z):
 xy=Eq(x,y);yz=Eq(y,z)
 return abst(xy,abst(yz,mp(mp(rho7(x,z,y),mp(sym(x,y),hyp(xy))),hyp(yz))))
def export(roots):
 fs=[];fi={};ps=[];pi={}
 def form(f):
  if f not in fi:fi[f]=len(fs);fs.append(f)
  return fi[f]
 def proof(t):
  if t in pi:return pi[t]
  args=[proof(x) for x in t.args] if t.rule=='MP' else [t.args[0],proof(t.args[1])] if t.rule=='GEN' else []
  pi[t]=len(ps);ps.append(dict(rule=t.rule,formula=form(t.form),args=args));return pi[t]
 rr={n:proof(t) for n,t in roots.items()}
 return dict(formulas=fs,proof_nodes=ps,roots=rr,scope='Schematic labels x,y,z and exact symbolic native binder weq(x,x). F=Rel(0,0).')
def main():
 roots={'equality_reflexivity':refl('x'),'equality_symmetry':sym('x','y'),'equality_transitivity':trans('x','y','z')}
 for t in roots.values():
  if assumptions(t):raise ValueError('open proof')
 out=Path(__file__).with_name('equality_proofs.json');out.write_text(json.dumps(export(roots),separators=(',',':'))+'\n')
 print(out)
if __name__=='__main__':main()
