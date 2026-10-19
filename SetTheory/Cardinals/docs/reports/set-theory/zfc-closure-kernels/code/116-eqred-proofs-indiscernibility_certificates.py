#!/usr/bin/env python3
"""Build closed certificates for the membership-defined equality bootstrap.
TAUT leaves are independently truth-table checked, using the already proved
canonical-V classical bridge. No equality vacuity, rho7, CP/GIC, or general
specialization/alpha rule is admitted as a leaf.
"""
from functools import cache
from itertools import product
from pathlib import Path
import json
from equality_certificates import P, I, Q, N, Ex, Eq, F, k, s, hyp, mp, abst, gen, assumptions, ident, mono, emono, rho1, rho2, rho6, export
R=lambda a,b:('rel',a,b)
And=lambda a,b:N(I(a,N(b)))
def weq(a,b):return 4*((a+b)*(a+b+1)//2+b)+3
@cache
def taut(f):return P('TAUT',f)
def prop(f,*ps):
    t=f
    for p in reversed(ps):t=I(p.form,t)
    t=taut(t)
    for p in ps:t=mp(t,p)
    return t
@cache
def sym(a,b):return P('SYM',I(Eq(a,b),Eq(b,a)))
@cache
def left(a,b,c):return P('rho5',I(Eq(a,b),I(R(a,c),R(b,c))))
@cache
def right(a,b,c):return P('rho3',I(Eq(a,b),I(R(c,a),R(c,b))))
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
    if a[0]=='rel':return P('vacRel',I(a,Q(i,a)))
    if a[0]=='imp':
        p,q=a[1:]
        vp,vq=vac(i,p),vac(i,q)
        vnp=vac_neg(i,p,vp)
        branch1=prop(I(N(p),Q(i,a)),vnp,mono(i,taut(I(N(p),a))))
        branch2=prop(I(q,Q(i,a)),vq,mono(i,taut(I(q,a))))
        return prop(I(a,Q(i,a)),branch1,branch2)
    if a[0]=='all':
        j,p=a[1:]
        comm=P('rho4',I(Q(j,Q(i,p)),Q(i,Q(j,p))))
        return prop(I(a,Q(i,a)),mono(j,vac(i,p)),comm)
    raise ValueError('No equality vacuity')
@cache
def leib(f,x,y):
    """Return Eq(x,y)->f->f' and Eq(x,y)->f'->f for QF Rel f."""
    d=Eq(x,y);g=rename(f,x,y)
    if f==F:return taut(I(d,I(f,g))),taut(I(d,I(g,f)))
    if f[0]=='rel':
        a,b=f[1:];aa=y if a==x else a;bb=y if b==x else b
        mid=R(aa,b)
        p1=left(x,y,b) if a==x else taut(I(d,I(f,mid)))
        p2=right(x,y,aa) if b==x else taut(I(d,I(mid,g)))
        r1=prop(I(d,I(mid,f)),sym(x,y),left(y,x,b)) if a==x else taut(I(d,I(mid,f)))
        r2=prop(I(d,I(g,mid)),sym(x,y),right(y,x,aa)) if b==x else taut(I(d,I(g,mid)))
        return prop(I(d,I(f,g)),p1,p2),prop(I(d,I(g,f)),r1,r2)
    if f[0]=='imp':
        p,q=f[1:];pf,pb=leib(p,x,y);qf,qb=leib(q,x,y)
        return prop(I(d,I(f,g)),pb,qf),prop(I(d,I(g,f)),pf,qb)
    raise ValueError('No quantified Leibniz bootstrap')
@cache
def all_imp_ex(i,a,b):
    h=mono(i,taut(I(I(a,b),I(N(b),N(a)))))
    return prop(I(Q(i,I(a,b)),I(Ex(i,a),Ex(i,b))),h,rho2(i,N(b),N(a)))
@cache
def qf_spec(x,y,f):
    if x==y:raise ValueError('Use self-specification for equal labels')
    g=rename(f,x,y)
    if x in labels(g):raise ValueError('Freshness after replacement failed')
    l=leib(f,x,y)[0]
    shuffle=prop(I(f,I(Eq(x,y),g)),l)
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
    s1,s2,d=E(c,a),E(c,b),E(a,b)
    out=[]
    for direction in (False,True):
        p,q,r=(body(c,a,w,direction),body(c,b,w,direction),body(a,b,w,direction))
        h1=prop(I(s1,Q(w,p)),aux(c,a,z1,w),taut(I(Ez(c,a,w),Q(w,p))))
        h2=prop(I(s2,Q(w,q)),aux(c,b,z2,w),taut(I(Ez(c,b,w),Q(w,q))))
        out.append(prop(I(s1,I(s2,Q(w,r))),h1,h2,all_taut2(w,p,q,r)))
    return prop(I(s1,I(s2,d)),*out,aux(a,b,w,z3))
@cache
def e_refl(a):
    z=weq(a,a)
    return prop(E(a,a),gen(z,taut(body(a,a,z))),gen(z,taut(body(a,a,z,True))))

def main():
    roots={}
    for a,b in ((0,1),(1,0),(1,1),(0,0)):
        z=weq(a,b);w=z+1
        roots[f'aux_{a}_{b}']=aux(a,b,z,w)
        roots[f'aux_reverse_{a}_{b}']=aux(a,b,w,z)
        roots[f'vac_internal_{a}_{b}']=e_vac(a,b,z)
        roots[f'vac_external_{a}_{b}']=e_vac(a,b,w)
        for c in (0,1,z):
            roots[f'rel_in_{a}_{b}_{c}']=e_rel(a,b,c)
            roots[f'rel_out_{a}_{b}_{c}']=e_rel(a,b,c,True)
    for a,b,c in product(range(2),repeat=3):roots[f'e_rho7_{a}_{b}_{c}']=e_rho7(a,b,c)
    roots['e_rho7_distinct']=e_rho7(0,1,2)
    roots['e_refl_zero']=e_refl(0)
    roots['qf_self_example']=qf_self(0,And(I(R(0,1),R(0,2)),I(R(0,2),R(0,1))))
    for p in roots.values():
        if assumptions(p):raise ValueError('Open root')
    d=export(roots)
    d['scope']='Numeric finite certificates for a uniform arbitrary-label construction. TAUT uses the previously checked canonical-V classical bridge. SYM is the proposed primitive symmetry row. No equality vacuity, rho7, CP/GIC, full specialization, or alpha rule is admitted.'
    d['expected_roots']={k:p.form for k,p in roots.items()}
    Path(__file__).with_name('indiscernibility_proofs.json').write_text(json.dumps(d,separators=(',',':'))+'\n')
    print(len(d['proof_nodes']),len(d['formulas']),len(roots))
if __name__=='__main__':main()
