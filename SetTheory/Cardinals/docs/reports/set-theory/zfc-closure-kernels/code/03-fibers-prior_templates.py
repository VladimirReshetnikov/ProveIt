#!/usr/bin/env python3
"""Baseline axiom constructors adapted from supplied report 1.

The original standalone output driver is omitted; run hull_templates.py
for the current comparison and output paths. No TM state counts are made.
"""
from syntax import *

def axioms() -> dict[str, F]:
    # Variables: A=0, x=1, y=2, b=3, z=4, C=5, one parameter p=6.
    A,x,y,b,z,C,p = range(7)
    phi = hole(x,y,A,p)
    def fiber_image(kernel: F) -> F:
        premise = ball(x,A,ex(b,all_(y,imp(phi,kernel))))
        image = ex(C,all_(y,iff(mem(y,C),bex(x,A,phi))))
        return alls([p,A],imp(premise,image))
    sbi = fiber_image(subset(y,b,z))
    bfi = fiber_image(or_(mem(y,b),subset(y,b,z)))
    mbi = fiber_image(mem(y,b))
    ext = alls([0,1],imp(same_members(0,1,2),eq(0,1)))
    ec = alls([0,1],imp(same_members(0,1,2),all_(3,imp(mem(0,3),mem(1,3)))))
    # CP: p=0,V=1,x=2,W=3,z=4,t=5,u=6.
    cp = all_(0,ex(1,and_(mem(0,1),ball(2,1,and_(subset(2,1,5),
        bex(3,1,all_(4,imp(subset(4,2,6),mem(4,3)))))))))
    empty = all_(2,neg(mem(2,1)))
    successor = all_(4,iff(mem(4,3),or_(mem(4,2),eq(4,2))))
    inf = ex(0,and_(bex(1,0,empty),ball(2,0,bex(3,0,successor))))
    # Same parameter/domain convention as the image-schema counts.
    functional = ball(x,A,alls([y,z],imp(and_(phi,hole(x,z,A,p)),eq(y,z))))
    pfi = alls([p,A],imp(functional,ex(C,all_(y,iff(mem(y,C),bex(x,A,phi))))))
    gic = alls([p,A],ex(C,and_(ball(x,A,all_(y,imp(phi,
        bex(z,C,hole(x,z,A,p))))),ball(y,C,ex(x,phi)))))
    return dict(Ext=ext, EC=ec, CP=cp, Inf=inf, SBI=sbi,
                BFI_member_or_subset=bfi, MBI_member_only=mbi, PFI=pfi, GIC=gic)
