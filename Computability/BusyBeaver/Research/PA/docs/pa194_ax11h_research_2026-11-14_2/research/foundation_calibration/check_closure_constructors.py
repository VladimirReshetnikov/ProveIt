#!/usr/bin/env python3
"""Independent AST-level replay of the NEW opening/closing proof constructors.

Uses exactly the ten in-place sequent rules of pinned Foundation's Basic.lean.
This tests constructor formulas and binder identities, not all natural codes.
The accompanying note supplies the uniform IΣ1 proof and numeric PR coding.
"""
from dataclasses import dataclass
from functools import lru_cache
from pathlib import Path
import argparse,json

def require(p,msg):
    if not p:raise AssertionError(msg)

def B(i):return ('b',i)
def F(i):return ('f',i)
def fn(i,*a):return ('func',i,tuple(a))
ZERO=fn(0)
def succ(t):return fn(1,t)
def add(s,t):return fn(2,s,t)
def eq(s,t):return ('rel',0,(s,t))
def AND(p,q):return ('and',p,q)
def OR(p,q):return ('or',p,q)
def ALL(p):return ('all',p)
def EX(p):return ('ex',p)
TOP=('true',);BOT=('false',)
def imp(p,q):return OR(neg(p),q)

def neg(p):
    t=p[0]
    if t=='true':return BOT
    if t=='false':return TOP
    if t=='rel':return ('nrel',p[1],p[2])
    if t=='nrel':return ('rel',p[1],p[2])
    if t=='and':return OR(neg(p[1]),neg(p[2]))
    if t=='or':return AND(neg(p[1]),neg(p[2]))
    if t=='all':return EX(neg(p[1]))
    if t=='ex':return ALL(neg(p[1]))
    raise AssertionError(t)

def tmap(t,b,f):
    if t[0]=='b':return b(t[1])
    if t[0]=='f':return f(t[1])
    return fn(t[1],*(tmap(s,b,f)for s in t[2]))

def shift(p):
    if p[0]in('true','false'):return p
    if p[0]in('rel','nrel'):
        return (p[0],p[1],tuple(tmap(t,B,lambda i:F(i+1))for t in p[2]))
    return (p[0],*(shift(s)for s in p[1:]))

def qvec(w):return [B(0)]+[tmap(t,lambda i:B(i+1),F)for t in w]

def subst(w,p):
    if p[0]in('true','false'):return p
    if p[0]in('rel','nrel'):
        return (p[0],p[1],tuple(tmap(t,lambda i:w[i] if i<len(w) else ZERO,F)for t in p[2]))
    if p[0]in('all','ex'):return(p[0],subst(qvec(w),p[1]))
    return(p[0],subst(w,p[1]),subst(w,p[2]))

def free(p):return subst([F(0)],shift(p))
def alls(k,b):
    for _ in range(k):b=ALL(b)
    return b
def fvec(k):return[F(i)for i in range(k)]
def tbv(t):
    if t[0]=='b':return t[1]+1
    if t[0]=='f':return 0
    return max((tbv(x)for x in t[2]),default=0)
def bv(p):
    if p[0]in('true','false'):return 0
    if p[0]in('rel','nrel'):return max((tbv(t)for t in p[2]),default=0)
    if p[0]in('all','ex'):return max(0,bv(p[1])-1)
    return max(bv(p[1]),bv(p[2]))

def seq(*a):return frozenset(a)
def shifted(s):return frozenset(shift(p)for p in s)

@dataclass(frozen=True)
class Proof:
    tag:int
    conclusion:frozenset
    args:tuple

@lru_cache(None)
def check(d):
    s=d.conclusion;a=d.args
    require(all(bv(p)==0 for p in s),'closed bound-variable scope')
    if d.tag==0:
        p,=a;require(p in s and neg(p)in s,'excluded middle')
    elif d.tag==1:require(TOP in s,'truth')
    elif d.tag==2:
        p,q,dp,dq=a;require(AND(p,q)in s,'and conclusion');check(dp);check(dq)
        require(dp.conclusion==s|seq(p)and dq.conclusion==s|seq(q),'and premises')
    elif d.tag==3:
        p,q,dp=a;require(OR(p,q)in s,'or conclusion');check(dp)
        require(dp.conclusion==s|seq(p,q),'or premise')
    elif d.tag==4:
        p,dp=a;require(ALL(p)in s,'all conclusion');check(dp)
        require(dp.conclusion==shifted(s)|seq(free(p)),'all premise')
    elif d.tag==5:
        p,t,dp=a;require(EX(p)in s and tbv(t)==0,'exists conclusion/term');check(dp)
        require(dp.conclusion==s|seq(subst([t],p)),'exists premise')
    elif d.tag==6:
        dp,=a;check(dp);require(dp.conclusion<=s,'weakening')
    elif d.tag==7:
        dp,=a;check(dp);require(shifted(dp.conclusion)==s,'shift')
    elif d.tag==8:
        p,dp,dq=a;check(dp);check(dq)
        require(dp.conclusion==s|seq(p)and dq.conclusion==s|seq(neg(p)),'cut')
    elif d.tag==9:
        p,=a;require(p in s,'hypothetical theory leaf')
    else:raise AssertionError('unknown tag')
    return True

def close_one(p,d):
    s=seq(ALL(p));w=Proof(6,seq(free(p))|shifted(s),(d,))
    return Proof(4,s,(p,w))

def open_one(p,d):
    u=shift(p);a=ALL(u);g=subst([F(0)],u);s=seq(g)
    d0=Proof(7,seq(a),(d,));d1=Proof(6,s|seq(a),(d0,))
    d3=Proof(0,s|seq(neg(g),neg(a)),(g,))
    d2=Proof(5,s|seq(neg(a)),(neg(u),F(0),d3))
    return Proof(8,s,(a,d1,d2))

def chain(k,b):
    require(bv(b)<=k and shift(b)==b,'closure preconditions')
    cs=[subst(fvec(j),alls(k-j,b))for j in range(k+1)]
    qs=[subst(qvec(fvec(j)),alls(k-j-1,b))for j in range(k)]
    require(cs[0]==alls(k,b)and cs[-1]==subst(fvec(k),b),'chain endpoints')
    for j,q in enumerate(qs):
        require(cs[j]==ALL(q)and free(q)==cs[j+1],('chain successor',k,j))
    return cs,qs

def open_proof(k,b,d):
    cs,qs=chain(k,b);require(d.conclusion==seq(cs[0]),'open proof initial')
    for j,q in enumerate(qs):
        d=open_one(q,d);check(d);require(d.conclusion==seq(cs[j+1]),'open proof stage')
    return d

def close_proof(k,b,d):
    cs,qs=chain(k,b);require(d.conclusion==seq(cs[-1]),'close proof initial')
    for j in reversed(range(k)):
        d=close_one(qs[j],d);check(d);require(d.conclusion==seq(cs[j]),'close proof stage')
    return d

def erase_exists_guard(b,e):
    """The literal logical proof of exists(b and e) -> exists(e).

    b,e may contain nested binders and arbitrary free parameters, but have
    bound-variable rank at most one. No theory leaves are used.
    """
    require(bv(b)<=1 and bv(e)<=1,'projection matrix scope')
    phi=OR(neg(b),neg(e));s=seq(ALL(phi),EX(e))
    r=shifted(s)|seq(free(phi));f=free(e)
    d0=Proof(0,r|seq(f,neg(free(b)),neg(f)),(f,))
    d1=Proof(3,r|seq(f),(neg(free(b)),neg(f),d0))
    d2=Proof(5,r,(shift(e),F(0),d1))
    d3=Proof(4,s,(phi,d2))
    conclusion=imp(EX(AND(b,e)),EX(e))
    d4=Proof(6,s|seq(conclusion),(d3,))
    d5=Proof(3,seq(conclusion),(ALL(phi),EX(e),d4))
    check(d5);return d5

def modus_ponens(p,q,dp,dpq):
    require(dp.conclusion==seq(p) and dpq.conclusion==seq(imp(p,q)),
            'modus ponens input conclusions')
    s=seq(q);f=imp(p,q)
    left=Proof(6,s|seq(f),(dpq,))
    r=s|seq(neg(f))
    right0=Proof(6,r|seq(p),(dp,))
    right1=Proof(0,r|seq(neg(q)),(q,))
    right=Proof(2,r,(p,neg(q),right0,right1))
    result=Proof(8,s,(f,left,right));check(result);return result

def implication_transitivity(a,x,y):
    """A fixed nine-node proof template, valid for arbitrary formulas."""
    aa=AND(a,neg(x));bb=AND(x,neg(y));cc=neg(a);dd=y
    s=seq(aa,bb,cc,dd)
    da=Proof(0,s|seq(a),(a,))
    dx=Proof(0,s|seq(neg(x),x),(x,))
    dy=Proof(0,s|seq(neg(x),neg(y)),(y,))
    db=Proof(2,s|seq(neg(x)),(x,neg(y),dx,dy))
    d=Proof(2,s,(a,neg(x),da,db))
    inner=OR(cc,dd);middle=OR(bb,inner);top=OR(aa,middle)
    dw=Proof(6,seq(top,aa,middle,bb,inner,cc,dd),(d,))
    di=Proof(3,seq(top,aa,middle,bb,inner),(cc,dd,dw))
    dm=Proof(3,seq(top,aa,middle),(bb,inner,di))
    dt=Proof(3,seq(top),(aa,middle,dm))
    require(top==imp(imp(a,x),imp(imp(x,y),imp(a,y))),
            'transitivity template formula')
    check(dt);return dt

def weaken_difference_axiom(b,e,a,old_proof):
    """Open two parameters, erase the existential guard, and close them.

    b,e are the three-bound-variable matrices before the inner existential;
    a is the two-bound-variable antecedent. old_proof proves the closed
    stronger sentence. This constructs the weaker current Foundation leaf.
    """
    require(bv(a)<=2 and bv(b)<=3 and bv(e)<=3,'finite leaf input scope')
    strong_body=imp(a,EX(AND(b,e)))
    weak_body=imp(a,EX(e))
    require(shift(strong_body)==strong_body,'finite leaf has no free parameters')
    opened=open_proof(2,strong_body,old_proof)
    aa=subst(fvec(2),a)
    bb=subst(qvec(fvec(2)),b)
    ee=subst(qvec(fvec(2)),e)
    x=EX(AND(bb,ee));y=EX(ee)
    require(opened.conclusion==seq(imp(aa,x)),'strong finite leaf opening')
    projection=erase_exists_guard(bb,ee)
    transitivity=implication_transitivity(aa,x,y)
    step=modus_ponens(imp(aa,x),imp(imp(x,y),imp(aa,y)),opened,transitivity)
    weak_open=modus_ponens(imp(x,y),imp(aa,y),projection,step)
    require(weak_open.conclusion==seq(subst(fvec(2),weak_body)),
            'weak finite leaf opening')
    return close_proof(2,weak_body,weak_open)

def closed_induction(m,q,additive=False):
    base=[ZERO]+[B(i)for i in range(m)]
    step=[add(B(0),succ(ZERO))if additive else succ(B(0))]+[B(i+1)for i in range(m)]
    return imp(subst(base,q),imp(ALL(imp(q,subst(step,q))),ALL(q)))

def ind(k,additive=False):
    return imp(subst([ZERO],k),imp(ALL(imp(k,subst([add(B(0),succ(ZERO))if additive else succ(B(0))],k))),ALL(k)))

def main(output):
    counts=dict(closure_chains=0,canonical_induction_readbacks=0,
                existential_guard_projections=0,current_finite_leaf_adapters=0,
                primitive_proof_nodes=0)
    for k in range(7):
        ts=[ZERO]+[B(i)for i in range(k)]
        atoms=[eq(t,u)for t in ts for u in ts]
        bodies=[TOP,BOT]+atoms+[OR(p,neg(p))for p in atoms]
        # Nested binders and noncontiguous support; no free variables.
        bodies += [ALL(imp(eq(B(0),ZERO),eq(B(k),B(0)))),
                   EX(OR(eq(B(0),succ(B(0))),eq(B(k),ZERO)))]
        for b in bodies:
            require(bv(b)<=k,'generated body bound')
            a=alls(k,b);base=Proof(9,seq(a),(a,));check(base)
            opened=open_proof(k,b,base);closed=close_proof(k,b,opened);check(closed)
            require(closed.conclusion==base.conclusion,'round-trip conclusion')
            counts['closure_chains']+=1
        for i in range(k+1):
            for j in range(k+1):
                q=OR(eq(B(i),B(j)),EX(eq(B(0),B(i+1))))
                m0=bv(ALL(q));require(m0<=k,'canonical bound')
                b0=closed_induction(m0,q);require(bv(b0)==m0 and shift(b0)==b0,'exact support')
                K=subst(qvec(fvec(k)),q);K0=subst(qvec(fvec(m0)),q)
                require(K==K0,'surplus-vector agreement')
                require(subst(fvec(m0),b0)==ind(K0),'successor readback')
                bp=closed_induction(k,q,True)
                require(subst(fvec(k),bp)==ind(K,True),'additive readback')
                # Exact constructor recovery used by additive_matrix_witness.
                require(bp[0]=='or'and bp[2][0]=='or'and bp[2][2]==ALL(q),'matrix extraction')
                counts['canonical_induction_readbacks']+=1
    # A fixed logical constructor, including complex translated-order guards.
    matrices=[TOP,BOT,eq(B(0),ZERO),eq(B(0),F(3)),
              EX(eq(B(0),add(B(1),F(2)))),
              ALL(OR(eq(B(0),B(1)),eq(F(5),F(5))))]
    for b in matrices:
        for e in matrices:
            erase_exists_guard(b,e)
            counts['existential_guard_projections']+=1
    # Current Foundation's unbounded addEqOfLt follows from its historical
    # bounded version. Use the exact translated antecedent/equation shape;
    # erasure is independent of which strict-upper-bound guard is used.
    antecedent=EX(eq(add(B(2),succ(B(0))),B(1)))
    equation=eq(add(B(2),B(0)),B(1))
    guards=[TOP,eq(B(0),B(1)),
            EX(eq(add(B(1),succ(B(0))),add(B(2),succ(ZERO)))),
            OR(eq(B(0),B(1)),EX(eq(add(B(1),succ(B(0))),B(2))))]
    for guard in guards:
        strong=alls(2,imp(antecedent,EX(AND(guard,equation))))
        hypothesis=Proof(9,seq(strong),(strong,));check(hypothesis)
        result=weaken_difference_axiom(guard,equation,antecedent,hypothesis)
        require(result.conclusion==seq(alls(2,imp(antecedent,EX(equation)))),
                'current addEqOfLt conclusion')
        check(result);counts['current_finite_leaf_adapters']+=1
    counts['primitive_proof_nodes']=check.cache_info().currsize
    result=dict(status='PASS',scope='AST instantiation of exact ten-rule constructors; uniform proof is written separately',
                fixed_rule_tags={'axL':0,'andIntro':2,'orIntro':3,'allIntro':4,
                                 'exsIntro':5,'wkRule':6,'shiftRule':7,'cutRule':8,'axm':9},
                counts=counts,closure_max_parameters=6,zero_parameter_case=True,
                surplus_and_missing_parameters=True,nested_binders=True,
                exact_translated_addEqOfLt_instance=True,
                finite_leaf_source='hypothetical old proof input; fixed finiteImageProof supplied separately',
                all_principal_formula_and_shifted_context_equalities_checked=True)
    Path(output).write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--output',default='closure_receipt.json');a=p.parse_args();main(a.output)
