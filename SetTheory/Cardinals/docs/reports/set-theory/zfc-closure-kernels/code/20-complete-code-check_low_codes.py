#!/usr/bin/env python3
"""Scope-aware finite checks of the low-code EPSC identities and padding.

These audits accompany the all-formula proof in low_code_epsc_theorem.tex;
finite evaluations do not themselves prove the identities for all models.
"""
from __future__ import annotations
import argparse
from functools import cache
import hashlib
import importlib.util
import json
from pathlib import Path
import sys

from hole_codec import codec, pair


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--output',type=Path)
    ap.add_argument('--matrices',type=int,default=10000)
    args=ap.parse_args()
    if not __debug__: ap.error('Run without -O')
    package=Path(__file__).resolve().parents[1]
    vendor=package/'vendor/epsc271'
    epsc_source=vendor/'full_equality_epsc.py'
    sys.path.insert(0,str(vendor))
    import theory_syntax as t
    modspec=importlib.util.spec_from_file_location('full_equality_epsc',epsc_source)
    mod=importlib.util.module_from_spec(modspec)
    modspec.loader.exec_module(mod)
    literal=mod.empty_psc(t,True)
    decode,encode,labels=codec(4)

    # Independent tree representation uses concrete quantifier labels.
    B=('bottom',); T=('truth',)
    R=lambda x,y:('rel',x,y)
    A=lambda x,p:('all',x,p)
    I=lambda p,q:('imp',p,q)
    N=lambda p:I(p,B)
    E=lambda x,p:N(A(x,N(p)))
    J=lambda p,q:N(I(p,N(q)))
    O=lambda p,q:I(N(p),q)
    S=lambda x,y,z:A(z,I(R(z,x),R(z,y)))

    def fixed(phi,k):
        lb=A(0,E(k,A(1,I(phi,S(1,k,0)))))
        empty=A(k,N(R(k,0)))
        closed=A(0,I(O(empty,R(0,k)),A(1,I(phi,R(1,k)))))
        support=A(1,I(R(1,k),E(0,phi)))
        return I(lb,E(k,J(support,closed)))

    def actual(form,c):
        if form==0:return T
        if form==1:return B
        if form=='c':return decode(c)
        kind,x,y=form
        var=lambda q:c if q=='c' else q
        if kind in ('rel','eq'):return(kind,var(x),var(y))
        if kind=='all':return A(var(x),actual(y,c))
        assert kind=='imp'
        return I(actual(x,c),actual(y,c))

    for c in (0,1,2,3,5,16,616):
        assert actual(literal,c)==fixed(decode(c),c)

    def rename_free(f,changes,bound=frozenset()):
        kind,*args=f
        if not args:return f
        x,y=args
        if kind in ('rel','eq'):
            return(kind,*(i if i in bound else changes.get(i,i) for i in (x,y)))
        if kind=='all':return A(x,rename_free(y,changes,bound|{x}))
        return I(rename_free(x,changes,bound),rename_free(y,changes,bound))

    def reference(phi):
        maximum=max(labels(phi),default=0)
        x,y,z,b,h=range(maximum+1,maximum+6)
        p=rename_free(phi,{0:x,1:y})
        lb=A(x,E(b,A(y,I(p,S(y,b,z)))))
        empty=A(z,N(R(z,x)))
        closed=A(x,I(O(empty,R(x,h)),A(y,I(p,R(y,h)))))
        support=A(y,I(R(y,h),E(x,p)))
        return I(lb,E(h,J(support,closed)))

    def alpha(f,env=()):
        kind,*args=f
        if not args:return f
        x,y=args
        var=lambda i:('bound',env.index(i)) if i in env else('free',i)
        if kind in ('rel','eq'):return(kind,var(x),var(y))
        if kind=='all':return(kind,alpha(y,(x,)+env))
        return(kind,alpha(x,env),alpha(y,env))

    direct=padding=0
    for c in range(args.matrices):
        phi=decode(c)
        if c>=2:
            assert alpha(fixed(phi,c))==alpha(reference(phi))
            direct+=1
        p=I(I(B,B),phi)
        cp=4*pair(16,c)
        assert encode(p)==cp and cp>=544 and all(i<cp for i in labels(p))
        assert alpha(fixed(p,cp))==alpha(reference(p))
        padding+=1

    graph_checks=ir_checks=0
    for n in (1,2,3):
        for mask in range(1<<(n*n)):
            @cache
            def sat(f,env):
                kind,*args=f
                if kind=='truth':return True
                if kind=='bottom':return False
                x,y=args
                if kind=='rel':return bool(mask & (1<<(env[x]*n+env[y])))
                if kind=='eq':return env[x]==env[y]
                if kind=='imp':return not sat(x,env) or sat(y,env)
                return all(sat(y,env[:x]+(v,)+env[x+1:]) for v in range(n))
            env=(0,0)
            ir=all(not(mask & (1<<(x*n+x))) for x in range(n))
            edge=mask!=0
            assert sat(actual(literal,1),env)==ir
            graph_checks+=1
            if ir:
                assert sat(actual(literal,0),env)==edge
                ir_checks+=1
    result=dict(actual_delivered_template_matches_independent_ast_cases=7,
        graph_models=graph_checks,G1_iff_IR_cases=graph_checks,
        IR_implies_G0_iff_edge_cases=ir_checks,
        decoded_matrix_direct_alpha_cases=direct,
        padded_matrix_alpha_cases=padding,
        padded_code_lower_bound=544,
        padding='Imp(Imp(Bottom,Bottom),phi)',
        epsc_source_sha256=hashlib.sha256(epsc_source.read_bytes()).hexdigest(),
        audit_source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        scope='Finite checks supporting the independent ordinary mathematical proof; no machine theorem')
    if args.output:
        args.output.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
    print(json.dumps(result,indent=2,sort_keys=True))


if __name__=='__main__':main()
