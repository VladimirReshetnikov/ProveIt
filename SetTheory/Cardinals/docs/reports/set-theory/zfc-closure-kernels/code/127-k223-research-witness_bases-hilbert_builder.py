#!/usr/bin/env python3
"""Minimal closed Hilbert proof builder with formula-DAG serialization.
No primitive equality existence, equality vacuity or symmetry rules occur here.
The generators provide their exact uniform-witness and optional-SYM leaves.
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
def rho2(i,a,b):return P('rho2',I(Q(i,I(a,b)),I(Q(i,a),Q(i,b))))
def rho6(i,a):return P('rho6',I(Ex(i,Q(i,a)),a))
def mono(i,t):
 a,b=t.form[1:];return mp(rho2(i,a,b),gen(i,t))
def contra(t):
 a,b=t.form[1:]
 return abst(N(b),abst(a,mp(hyp(N(b)),mp(t,hyp(a)))))
def emono(i,t):return contra(mono(i,contra(t)))
def export(roots):
 fs=[];fi={};ps=[];pi={}
 def form(f):
  if f not in fi:
   if f[0]=='imp':record=['imp',form(f[1]),form(f[2])]
   elif f[0]=='all':record=['all',f[1],form(f[2])]
   else:record=list(f)
   fi[f]=len(fs);fs.append(record)
  return fi[f]
 def proof(t):
  if t in pi:return pi[t]
  args=[proof(x) for x in t.args] if t.rule=='MP' else [t.args[0],proof(t.args[1])] if t.rule=='GEN' else []
  pi[t]=len(ps);ps.append(dict(rule=t.rule,formula=form(t.form),args=args));return pi[t]
 rr={n:proof(t) for n,t in roots.items()}
 return dict(format='formula_dag_v1',formulas=fs,proof_nodes=ps,roots=rr,scope='Closed Hilbert proof DAG. F=Rel(0,0); generator provides the exact leaf-family scope.')
