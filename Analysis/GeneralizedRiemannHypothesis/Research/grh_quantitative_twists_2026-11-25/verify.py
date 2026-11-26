#!/usr/bin/env python3
"""Exact arithmetic tests of the shell estimate and conductor-exponent bound.
Only Python standard library. A root represented by (h,a) is zeta_{p^h}^a-1.
The synthetic polynomials are actual monic polynomials over Qp-bar, not just
formal Newton polygons. Infinity (a vanishing polynomial) is represented by None.
These tests corroborate, but do not prove, the general theorem.
"""
from fractions import Fraction as F
from functools import lru_cache
from math import prod, log10, log, floor
import random


def phi(p,h): return (p-1)*p**(h-1)
def rad(p,h): return F(1,phi(p,h))
def vp(p,a):
    assert a!=0
    v=0
    while a%p==0: v+=1; a//=p
    return v
@lru_cache(None)
def units(p,h): return tuple(a for a in range(1,p**h) if a%p)
def distance(p,h,a,b):
    return None if a==b else rad(p,h-vp(p,a-b))
def val(p,roots,h,a):
    r=rad(p,h); result=F(0)
    for k,b in roots:
        if k==h:
            d=distance(p,h,a,b)
            if d is None:return None
            result+=d
        else: result+=min(r,rad(p,k))
    return result

def H_bound(p,h0,B,delta,eta=F(1)):
    """Smallest integer H>=h0 satisfying the exact sufficient inequality.
    ((H+C+1)/(h0+C))**(c*eta) >= product(1+c*B_i/delta_i).
    Comparison uses integers/rationals only, never floating point.
    """
    c=F(p-1,p); C=1+max((b+d for b,d in zip(B,delta)),default=F(0)); P=prod(1+c*b/d for b,d in zip(B,delta)); t=c*eta
    def ok(H):return ((H+C+1)/(h0+C))**t.numerator >= P**t.denominator
    lo=h0; hi=h0
    while not ok(hi):hi*=2
    while lo<hi:
        mid=(lo+hi)//2
        if ok(mid):hi=mid
        else:lo=mid+1
    return lo

def test_derivative():
    count=0
    for p,maxh in [(2,7),(3,5),(5,3),(7,2)]:
        for h in range(1,maxh+1):
            a=units(p,h)[0]
            assert sum(distance(p,h,a,b) for b in units(p,h) if a!=b)==h-F(1,p-1)
            for C in (F(1,50), F(1,2),F(3),F(21,2)):
                r=rad(p,h)
                tot=sum(C if a==b else min(C,distance(p,h,a,b)-r) for b in units(p,h))
                assert tot<=C+h
                count+=1
    return count


def test_packets():
    rng=random.Random(28451); tested=0; blocked=0; max_found=0; shell_checks=0
    for p,L in [(2,6),(3,4),(5,3)]:
        examples=[]
        # Complete shell factors force exact zeros at all those orders.
        for k in range(1,L):
            examples.append([[(h,a) for h in range(1,k+1) for a in units(p,h)]])
        for _ in range(120):
            packet=[]
            for _i in range(rng.randint(1,4)):
                roots=[]
                for _j in range(rng.randint(0,22)):
                    h=rng.randint(1,L-1);roots.append((h,rng.choice(units(p,h))))
                packet.append(roots)
            examples.append(packet)
        for packet in examples:
            h0=1; B=[sum((rad(p,h) for h,_ in roots),F(0)) for roots in packet]
            delta=[rng.choice((F(1,20),F(1,3),F(1))) for _ in B]
            eta=rng.choice((F(1),F(1,2),F(1,4)));C=1+max(b+d for b,d in zip(B,delta));c=F(p-1,p)
            H=H_bound(p,h0,B,delta,eta); W=[F(0) for _ in B]; found=None
            for h in range(1,L+1):
                z=units(p,h); r=rad(p,h); ws=[r*sum(k==h for k,_ in roots) for roots in packet]
                slacks=[B[i]-sum((min(r,rad(p,k)) for k,_ in roots),F(0)) for i,roots in enumerate(packet)]
                assert all(slack>=c*w for slack,w in zip(slacks,W))
                sums=[F(0) for _ in B]; bad=0
                for a in z:
                    fails=False
                    for i,roots in enumerate(packet):
                        vv=val(p,roots,h,a)
                        fails|=(vv is None or vv>B[i]+delta[i])
                        ex=sum((C if a==b else min(C,distance(p,h,a,b)-r) for k,b in roots if k==h),F(0))
                        sums[i]+=ex
                        if vv is None or vv>B[i]+delta[i]:assert ex>slacks[i]+delta[i]
                    bad+=fails
                for s,w in zip(sums,ws):assert s/len(z)<=w*(h+C)
                if F(bad,len(z))>=eta:
                    blocked+=1
                    assert sum((w/(d+c*old) for w,d,old in zip(ws,delta,W)),F(0))>eta/(h+C)
                    prev=prod(1+c*old/d for old,d in zip(W,delta))
                    new=prod(1+c*(old+w)/d for old,w,d in zip(W,ws,delta))
                    assert new/prev>1+c*eta/(h+C)
                elif found is None:found=h
                W=[a+b for a,b in zip(W,ws)]; shell_checks+=1
            # All roots were chosen below L: at L, every evaluation is good.
            assert found is not None and found<=H
            max_found=max(max_found,found); tested+=1
    return tested,shell_checks,blocked,max_found


def print_table():
    print('p,n,B_each,delta_each,h0,eta,H_new,log10(H_old+1)_lower')
    for p,n,b,d,h0,eta in [(2,1,F(1),F(1,10),2,F(1)),(3,1,F(1),F(1,100),2,F(1)),(3,1,F(1),F(1,100),2,F(1,2)),(5,2,F(1),F(1,100),2,F(1)),(3,3,F(2),F(1,1000),3,F(1))]:
        H=H_bound(p,h0,[b]*n,[d]*n,eta)
        # Source harmonic criterion for the total product uses B_total and delta.
        # For eta<1 this is only an existence comparison, not a density bound.
        lower=log10(h0)+float(n*b/d)/log(10)
        print(f'{p},{n},{b},{d},{h0},{eta},{H},{lower:.4f}')

if __name__=='__main__':
    print('Derivative / capped averaging checks:',test_derivative())
    a,b,c,d=test_packets()
    print(f'Exact cyclotomic-root packet tests: {a}; shell checks: {b}; bad-shell recurrence checks: {c}; largest first successful shell: {d}')
    print_table()
    print('All checks passed.')
