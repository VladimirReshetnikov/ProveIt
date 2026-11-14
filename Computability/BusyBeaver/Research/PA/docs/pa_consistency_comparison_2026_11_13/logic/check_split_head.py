#!/usr/bin/env python3
"""Finite Hilbert certificates for splitting the PA196 B/explosion head.

Uses K,S,Peirce, all derived from the restricted rho8 basis in
M6/Logic/RestrictedImplication.lean.  No quantifier rule is used: X denotes
U(D,U(D,H)->f), treated as one propositional expression.
"""
from dataclasses import dataclass
import json


def I(a,b): return (a,b)


def k(a,b): return I(a,I(b,a))
def s(a,b,c): return I(I(a,I(b,c)), I(I(a,b),I(a,c)))
def peirce(a,b): return I(I(I(a,b),a),a)

@dataclass(frozen=True)
class Proof:
    formula: object
    rule: str
    args: tuple


def hyp(a): return Proof(a,'hyp',())
def K(a,b): return Proof(k(a,b),'K',(a,b))
def S(a,b,c): return Proof(s(a,b,c),'S',(a,b,c))
def P(a,b): return Proof(peirce(a,b),'Peirce',(a,b))
def mp(p,q):
    assert isinstance(q.formula,tuple) and q.formula[0] == p.formula
    return Proof(q.formula[1],'MP',(p,q))


def ident(a):
    return mp(K(a,a), mp(K(a,I(a,a)), S(a,I(a,a),a)))


def deduce(p,a):
    if p.rule=='hyp' and p.formula==a:
        return ident(a)
    if p.rule!='MP':
        return mp(p,K(p.formula,a))
    minor,major=p.args
    return mp(deduce(minor,a),mp(deduce(major,a),S(a,minor.formula,p.formula)))


def check(p,hyps,seen=None):
    if seen is None: seen=set()
    if id(p) in seen: return
    seen.add(id(p))
    if p.rule=='hyp': assert p.formula in hyps
    elif p.rule=='K': assert p.formula == k(*p.args)
    elif p.rule=='S': assert p.formula == s(*p.args)
    elif p.rule=='Peirce': assert p.formula == peirce(*p.args)
    elif p.rule=='MP':
        a,b=p.args
        check(a,hyps,seen); check(b,hyps,seen)
        assert b.formula == I(a.formula,p.formula)
    else: raise AssertionError('unknown rule')


def stats(p):
    seen=set(); counts={}
    def walk(q):
        if id(q) in seen:return
        seen.add(id(q)); counts[q.rule]=counts.get(q.rule,0)+1
        if q.rule=='MP':
            for a in q.args:walk(a)
    walk(p)
    return {'nodes':len(seen),'rules':counts}


def show(f):
    return str(f) if not isinstance(f,tuple) else '('+show(f[0])+' -> '+show(f[1])+')'

f,H,X,A,Y='f','H','X','A','Y'
O=I(I(X,f),H)
B=I(I(H,f),X)
# E_H, B |- O
p,n=hyp(I(X,f)),hyp(I(H,f))
x=mp(n,hyp(B))
h=mp(mp(x,p),hyp(I(f,H)))
h=mp(deduce(h,I(H,f)),P(H,f))
new_to_old=deduce(h,I(X,f))
check(new_to_old,{I(f,H),B})
assert new_to_old.formula==O
# E_X, O |- B
n,q=hyp(I(H,f)),hyp(I(X,f))
h=mp(q,hyp(O))
x=mp(mp(h,n),hyp(I(f,X)))
x=mp(deduce(x,I(X,f)),P(X,f))
old_to_new=deduce(x,I(H,f))
check(old_to_new,{I(f,X),O})
assert old_to_new.formula==B
# O_A = ((Y->f)->A) |- f->A, without explosion already available.
oa=I(I(Y,f),A)
a=mp(mp(hyp(f),K(f,Y)),hyp(oa))
old_to_explosion=deduce(a,f)
check(old_to_explosion,{oa})
assert old_to_explosion.formula==I(f,A)

if __name__=='__main__':
    print(json.dumps({name:{'conclusion':show(p.formula),**stats(p)}
      for name,p in [('new_to_old',new_to_old),('old_to_new',old_to_new),
        ('old_to_explosion',old_to_explosion)]},indent=2))
