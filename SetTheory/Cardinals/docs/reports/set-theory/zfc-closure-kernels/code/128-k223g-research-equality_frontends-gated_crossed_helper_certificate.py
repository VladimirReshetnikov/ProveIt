#!/usr/bin/env python3
"""Finite closed certificates for full gated SINGLE crossed equality.

The only new primitive helper is
  C1(a,b,c): Eq(a,b) -> All_c Eq(b,a), c != a,b.
No rho7, primitive symmetry, equality vacuity, substitution, or alpha rule
is admitted as a proof leaf. All proof nodes are exported, independently
checked, reloaded from JSON, and checked again. The shared representation
and exporter are local stdlib-only code in combined_helper_certificate.py.

TAUT leaves abbreviate the classical propositional calculus already derived
from the unchanged original rho8 and rho6. Rel(0,0) is designated bottom, including
when its raw variable label 0 is bound. No closed-bottom assumption is made.
"""
from functools import cache
from itertools import product
from pathlib import Path
import hashlib, json
from combined_helper_certificate import (
    P, I, Q, N, Ex, Eq, F, And, assumptions, mp, gen, taut, prop,
    rho1, rho2, rho6, mono, all_imp_ex, serial, export, read_export,
    prop_atoms, eval_prop,
)

R=lambda a,b:('rel',a,b)
def weq(a,b):return 4*((a+b)*(a+b+1)//2+b)+3

@cache
def contra(t):
    a,b=t.form[1:]
    return prop(I(N(b),N(a)),t)
@cache
def emono(i,t):return contra(mono(i,contra(t)))
@cache
def c1(a,b,z):
    if z in (a,b):raise ValueError('C1 gate')
    return P('C1',I(Eq(a,b),Q(z,Eq(b,a))),(a,b,z))
@cache
def double_elim(i,f):
    return prop(I(Q(i,Q(i,f)),f),serial(i,Q(i,f)),rho6(i,f))
@cache
def left(a,b,c):return P('rho5',I(Eq(a,b),I(R(a,c),R(b,c))),(a,b,c))
@cache
def right(a,b,c):return P('rho3',I(Eq(a,b),I(R(c,a),R(c,b))),(a,b,c))
@cache
def labels(f):
    if f==F:return frozenset()
    if f[0] in ('rel','eq'):return frozenset(f[1:])
    if f[0]=='imp':return labels(f[1])|labels(f[2])
    return frozenset((f[1],))|labels(f[2])
@cache
def rename(f,x,y):
    if f==F:return F
    if f[0]=='rel':return R(*(y if a==x else a for a in f[1:]))
    if f[0]=='imp':return I(rename(f[1],x,y),rename(f[2],x,y))
    raise ValueError('Only quantifier-free membership renaming is available')
@cache
def vac_neg(i,a,v):
    exelim=prop(I(Ex(i,a),a),emono(i,v),rho6(i,a))
    return prop(I(N(a),Q(i,N(a))),exelim)
@cache
def vac(i,a):
    if a==F:return taut(I(a,Q(i,a)))
    if i in labels(a):raise ValueError(('not syntactically fresh',i,a))
    if a[0]=='rel':return P('vacRel',I(a,Q(i,a)),(i,a[1],a[2]))
    if a[0]=='imp':
        p,q=a[1:]
        vp,vq=vac(i,p),vac(i,q)
        vnp=vac_neg(i,p,vp)
        branch1=prop(I(N(p),Q(i,a)),vnp,mono(i,taut(I(N(p),a))))
        branch2=prop(I(q,Q(i,a)),vq,mono(i,taut(I(q,a))))
        return prop(I(a,Q(i,a)),branch1,branch2)
    if a[0]=='all':
        j,p=a[1:]
        comm=P('rho4',I(Q(j,Q(i,p)),Q(i,Q(j,p))),(j,i,p))
        return prop(I(a,Q(i,a)),mono(j,vac(i,p)),comm)
    raise ValueError('No equality vacuity')
@cache
def fresh_box_elim(i,f):
    """All_i f -> f for membership-only f with syntactically fresh i."""
    return prop(I(Q(i,f),f),mono(i,vac(i,f)),double_elim(i,f))
@cache
def back_congruence(a,b,t,outgoing=False):
    """Eq(a,b) conditionally reverses one membership argument.

    The proof supplies no primitive Eq symmetry. A fresh C1 binder is
    eliminated from the membership implication with fresh_box_elim.
    """
    A=I(R(b,t),R(a,t)) if outgoing else I(R(t,b),R(t,a))
    if a==b:return taut(I(Eq(a,b),A))
    h=max(a,b,t)+1
    reverse_atom=(left if outgoing else right)(b,a,t)
    return prop(I(Eq(a,b),A),c1(a,b,h),mono(h,reverse_atom),fresh_box_elim(h,A))
@cache
def leib(f,x,y):
    """Both Eq(x,y)-conditional directions, only for QF membership formulas."""
    d=Eq(x,y);g=rename(f,x,y)
    if f==F:return taut(I(d,I(f,g))),taut(I(d,I(g,f)))
    if f[0]=='rel':
        a,b=f[1:];aa=y if a==x else a;bb=y if b==x else b
        mid=R(aa,b)
        p1=left(x,y,b) if a==x else taut(I(d,I(f,mid)))
        p2=right(x,y,aa) if b==x else taut(I(d,I(mid,g)))
        r1=back_congruence(x,y,b,True) if a==x else taut(I(d,I(mid,f)))
        r2=back_congruence(x,y,aa,False) if b==x else taut(I(d,I(g,mid)))
        return prop(I(d,I(f,g)),p1,p2),prop(I(d,I(g,f)),r1,r2)
    if f[0]=='imp':
        p,q=f[1:];pf,pb=leib(p,x,y);qf,qb=leib(q,x,y)
        return prop(I(d,I(f,g)),pb,qf),prop(I(d,I(g,f)),pf,qb)
    raise ValueError('No quantified Leibniz bootstrap')
@cache
def qf_spec(x,y,f):
    if x==y:raise ValueError('Use self-specialization for equal labels')
    g=rename(f,x,y)
    if x in labels(g):raise ValueError('Freshness after replacement failed')
    shuffle=prop(I(f,I(Eq(x,y),g)),leib(f,x,y)[0])
    lift=mono(x,shuffle)
    exelim=prop(I(Ex(x,g),g),emono(x,vac(x,g)),rho6(x,g))
    return prop(I(Q(x,f),g),lift,all_imp_ex(x,Eq(x,y),g),rho1(x,y),exelim)
@cache
def qf_self(x,f):
    z=max(labels(f)|{x})+1
    g=rename(f,x,z)
    first=qf_spec(x,z,f)
    lifted=prop(I(Q(x,f),Q(z,g)),vac(z,Q(x,f)),mono(z,first))
    second=qf_spec(z,x,g)
    if second.form[2]!=f:raise ValueError('Fresh detour failed')
    return prop(I(Q(x,f),f),lifted,second)
@cache
def body(a,b,z,outgoing=False):
    p,q=(R(a,z),R(b,z)) if outgoing else (R(z,a),R(z,b))
    return And(I(p,q),I(q,p))
@cache
def Ez(a,b,z):
    if z in (a,b):raise ValueError('Unsafe indiscernibility binder')
    return And(Q(z,body(a,b,z)),Q(z,body(a,b,z,True)))
def E(a,b):return Ez(a,b,weq(a,b))
@cache
def aux(a,b,z,w):
    src,dst=Ez(a,b,z),Ez(a,b,w)
    if z==w:return taut(I(src,dst))
    outs=[]
    for out in (False,True):
        bz=body(a,b,z,out);bw=body(a,b,w,out)
        sp=qf_spec(z,w,bz)
        if sp.form[2]!=bw:raise ValueError('Wrong binder transport')
        h=prop(I(src,bw),taut(I(src,Q(z,bz))),sp)
        outs.append(prop(I(src,Q(w,bw)),vac(w,src),mono(w,h)))
    return prop(I(src,dst),*outs)
@cache
def e_refl(a):
    z=weq(a,a)
    return prop(E(a,a),gen(z,taut(body(a,a,z))),gen(z,taut(body(a,a,z,True))))
@cache
def eq_to_e(a,b):
    e=Eq(a,b)
    if a==b:return prop(I(e,E(a,b)),e_refl(a))
    z=weq(a,b);f=Eq(b,a);outs=[]
    for outgoing in (False,True):
        B=body(a,b,z,outgoing)
        congruence=left if outgoing else right
        f_to_body=prop(I(f,B),back_congruence(b,a,z,outgoing),congruence(b,a,z))
        outs.append(prop(I(e,Q(z,B)),c1(a,b,z),mono(z,f_to_body)))
    at_z=prop(I(e,Ez(a,b,z)),*outs)
    return prop(I(e,E(a,b)),at_z,aux(a,b,z,weq(a,b)))
@cache
def e_exists(a,b):return mp(emono(a,eq_to_e(a,b)),rho1(a,b))
@cache
def e_vac(a,b,i):
    if i in (a,b):raise ValueError('Illegal equality vacuity gate')
    z=weq(a,b);w=max(a,b,i,z)+1
    return prop(I(E(a,b),Q(i,E(a,b))),aux(a,b,z,w),vac(i,Ez(a,b,w)),mono(i,aux(a,b,w,z)))
@cache
def e_rel(a,b,c,outgoing=False):
    z=weq(a,b);w=max(a,b,c,z)+1
    B=body(a,b,w,outgoing)
    p,q=(R(a,c),R(b,c)) if outgoing else (R(c,a),R(c,b))
    return prop(I(E(a,b),I(p,q)),aux(a,b,z,w),taut(I(Ez(a,b,w),Q(w,B))),qf_spec(w,c,B))
@cache
def all_taut2(w,p,q,r):
    h=gen(w,taut(I(p,I(q,r))))
    return prop(I(Q(w,p),I(Q(w,q),Q(w,r))),h,rho2(w,p,I(q,r)),rho2(w,q,r))
@cache
def e_rho7(a,b,c):
    z1,z2,z3=weq(c,a),weq(c,b),weq(a,b)
    w=max(a,b,c,z1,z2,z3)+1
    s1,s2,d=E(c,a),E(c,b),E(a,b);outs=[]
    for direction in (False,True):
        p,q,r=body(c,a,w,direction),body(c,b,w,direction),body(a,b,w,direction)
        h1=prop(I(s1,Q(w,p)),aux(c,a,z1,w),taut(I(Ez(c,a,w),Q(w,p))))
        h2=prop(I(s2,Q(w,q)),aux(c,b,z2,w),taut(I(Ez(c,b,w),Q(w,q))))
        outs.append(prop(I(s1,I(s2,Q(w,r))),h1,h2,all_taut2(w,p,q,r)))
    return prop(I(s1,I(s2,d)),*outs,aux(a,b,w,z3))

@cache
def check_taut(f):
    atoms=sorted(prop_atoms(f),key=repr)
    if any(not eval_prop(f,dict(zip(atoms,bits))) for bits in product((False,True),repeat=len(atoms))):
        raise ValueError('Nontautological TAUT leaf')

def check(t,seen,counts):
    if t in seen:return
    seen.add(t);counts[t.rule]=counts.get(t.rule,0)+1
    r,f=t.rule,t.form
    if r=='MP':
        p,q=t.args
        if p.form!=I(q.form,f):raise ValueError('Invalid MP')
        check(p,seen,counts);check(q,seen,counts)
    elif r=='GEN':
        z,p=t.args
        if assumptions(p) or f!=Q(z,p.form):raise ValueError('Open or malformed GEN')
        check(p,seen,counts)
    elif r=='TAUT':check_taut(f)
    elif r=='rho1':
        z=f[1][1];atom=f[1][2][1]
        if atom[0]!='eq' or atom[1]!=z or f!=Ex(z,atom):raise ValueError('rho1')
    elif r=='rho2':
        z=f[1][1];a=f[1][2][1];b=f[1][2][2]
        if f!=I(Q(z,I(a,b)),I(Q(z,a),Q(z,b))):raise ValueError('rho2')
    elif r=='rho3':
        a,b,c=t.args
        if f!=I(Eq(a,b),I(R(c,a),R(c,b))):raise ValueError('rho3')
    elif r=='rho4':
        a,b,c=t.args
        if f!=I(Q(a,Q(b,c)),Q(b,Q(a,c))):raise ValueError('rho4')
    elif r=='rho5':
        a,b,c=t.args
        if f!=I(Eq(a,b),I(R(a,c),R(b,c))):raise ValueError('rho5')
    elif r=='rho6':
        a=f[2];z=f[1][1][1]
        if f!=I(Ex(z,Q(z,a)),a):raise ValueError('rho6')
    elif r=='vacRel':
        z,a,b=t.args
        if z in (a,b) or f!=I(R(a,b),Q(z,R(a,b))):raise ValueError('vacRel')
    elif r=='C1':
        a,b,z=t.args
        if z in (a,b) or f!=I(Eq(a,b),Q(z,Eq(b,a))):
            raise ValueError('Invalid C1 helper or gate')
    else:raise ValueError('Unpermitted rule '+r)

def main():
    roots={};groups={}
    pairs=[(0,0),(0,1),(1,0),(1,1),(3,999)]
    for a,b in pairs:
        for name,t in [('eq_to_e',eq_to_e(a,b)),('e_exists',e_exists(a,b))]:
            roots[f'{name}_{a}_{b}']=t
        for out in [False,True]:roots[f'back_congruence_{a}_{b}_{out}']=back_congruence(a,b,weq(a,b),out)
    for a,b in [(0,1),(1,1)]:
        k=weq(a,b)
        roots[f'e_vacuity_collision_{a}_{b}']=e_vac(a,b,k)
        for c in [0,k]:
            for out in [False,True]:roots[f'e_congruence_{a}_{b}_{c}_{out}']=e_rel(a,b,c,out)
    for a,b,c in [(0,1,2),(0,0,0),(0,1,0)]:roots[f'e_euclidean_{a}_{b}_{c}']=e_rho7(a,b,c)
    for name,t in roots.items():
        if assumptions(t):raise ValueError('Open root '+name)
        seen=set();counts={};check(t,seen,counts)
        groups[name]={'nodes':len(seen),'rules':counts}
    data=export(roots)
    data['scope']='Finite closed proof DAGs. Full gated C1 Eqab -> All_c Eqba; no T, C2, rho7, SYM, Eq-vacuity, alpha, or substitution leaves. TAUT uses unchanged rho8/rho6 classical bridge.'
    raw=(json.dumps(data,separators=(',',':'))+'\n').encode()
    out=Path(__file__).with_name('gated_crossed_helper_proofs.json');out.write_bytes(raw)
    reloaded=read_export(json.loads(raw));seen=set();counts={}
    for name,t in reloaded.items():
        if t.form!=roots[name].form:raise ValueError('Reloaded root mismatch')
        check(t,seen,counts)
    receipt={'status':'PASS','proof_sha256':hashlib.sha256(raw).hexdigest(),
             'proof_nodes':len(data['proof_nodes']),'formulas':len(data['formulas']),
             'roots':groups,'total_rules':counts,
             'scope':data['scope']+' This is not a machine-table equivalence theorem or a new proof-assistant endpoint.'}
    Path(__file__).with_name('gated_crossed_helper_receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps({k:v for k,v in receipt.items() if k!='roots'},indent=2))
if __name__=='__main__':main()
