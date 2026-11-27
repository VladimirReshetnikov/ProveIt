#!/usr/bin/env python3
"""Finite checks of the local filter and primitive-conductor weight.

Standard library only. Algebraic tests use exact rationals and integer
polynomials. Prime-sum examples use floating point logarithms; they are
illustrations, not a test of the infinite analytic theorem.
"""
from fractions import Fraction as Q
from functools import lru_cache
from math import gcd, isqrt, log, fsum, sqrt
from pathlib import Path
import csv


def coeff(r):
    return (-Q(1), r+2, -2*r-1, r)


def ramp(r, u):
    return sum(c*max(Q(0), 1/u-r**(-j)) for j,c in enumerate(coeff(r)))


def kernel(r, u):
    if u <= 1 or u >= r**3:
        return Q(0)
    if u <= r:
        return 1/u-1
    if u <= r*r:
        return 2/r-(r+1)/u
    return r/u-1/r**2


def test_filter():
    count=0
    for r in map(Q, ['101/100','11/10','5/4','3/2','2','3','7/2']):
        c=coeff(r)
        assert sum(c)==sum(j*c[j] for j in range(4))==sum(c[j]*r**(-j) for j in range(4))==0
        # Exact transform identities at the polynomial level.
        for z in [Q(-2),Q(0),Q(1,3),1/r,Q(1),Q(4)]:
            assert sum(c[j]*z**j for j in range(4))==(z-1)**2*(r*z-1)
        pts={Q(1,2),Q(1),r,r*r,r**3,r**3+1,r*(r+1)/2}
        pts.update(r**3*Q(k,200) for k in range(1,240))
        for u in sorted(pts):
            assert kernel(r,u)==ramp(r,u),(r,u)
            if 1<u<r*(r+1)/2:
                assert kernel(r,u)<0
            elif r*(r+1)/2<u<r**3:
                assert kernel(r,u)>0
            count+=1
    print(f'Exact filter tests: {count} rational kernel/sign identities; 7 scale ratios; cancellation and multiplier identities passed.')


def divisors(n):
    return [d for d in range(1,n+1) if n%d==0]


def mobius(n):
    m=1
    p=2
    while p*p<=n:
        if n%p==0:
            n//=p
            if n%p==0: return 0
            m=-m
        p+=1
    return -m if n>1 else m


def units(q):
    return [x for x in range(q) if gcd(x,q)==1]


def phi(q):
    return len(units(q))


def primitive_weight(q,n):
    if gcd(q,n)!=1: return 0
    return sum(mobius(q//d)*phi(d) for d in divisors(q) if (n-1)%d==0)


def enumerate_characters(q):
    """All homomorphisms U(q)-> roots of unity of order phi(q),
    independently constructed by subgroup extension, no Dirichlet formulas."""
    U=units(q); N=len(U)
    chars=[{1%q:0}]
    while len(chars[0])<N:
        H=set(chars[0]); g=next(x for x in U if x not in H)
        powers=[1%q]; x=g; k=1
        while x not in H:
            powers.append(x); x=x*g%q; k+=1
        # g^k is in H. Extend each homomorphism to <H,g>.
        new=[]
        for h in chars:
            for e in range(N):
                if (k*e-h[x])%N==0:
                    row={(u*v)%q:(a+j*e)%N for u,a in h.items() for j,v in enumerate(powers)}
                    assert len(row)==k*len(H)
                    new.append(row)
        chars=new
    assert len(chars)==N
    for ch in chars:
        assert all(ch[(a*b)%q]==(ch[a]+ch[b])%N for a in U for b in U)
    return chars


def is_primitive(q,ch):
    for d in divisors(q)[:-1]:
        fibers={}
        for n,e in ch.items():
            fibers.setdefault(n%d,set()).add(e)
        if all(len(v)==1 for v in fibers.values()): return False
    return True


def trim(a):
    while len(a)>1 and a[-1]==0: a.pop()
    return a


def divmod_monic(a,b):
    a=trim(list(a)); b=trim(list(b)); assert b[-1]==1
    out=[0]*max(1,len(a)-len(b)+1)
    while len(a)>=len(b) and a!=[0]:
        k=len(a)-len(b); c=a[-1]; out[k]=c
        for j,t in enumerate(b): a[k+j]-=c*t
        trim(a)
    return trim(out),a


@lru_cache(None)
def cyclotomic(n):
    a=[-1]+[0]*(n-1)+[1]
    for d in divisors(n)[:-1]:
        a,rem=divmod_monic(a,cyclotomic(d)); assert rem==[0]
    return tuple(a)


def test_primitive():
    total=0
    for q in range(1,37):
        N=phi(q); chars=enumerate_characters(q)
        prim=[c for c in chars if is_primitive(q,c)]
        for n in range(q):
            poly=[0]*N
            if gcd(n,q)==1:
                for ch in prim: poly[ch[n]]+=1
            poly[0]-=primitive_weight(q,n)
            # A polynomial vanishes at a primitive Nth root iff divisible
            # by the cyclotomic polynomial. Entire check is exact.
            assert divmod_monic(poly,cyclotomic(N))[1]==[0],(q,n)
            total+=1
        assert len(prim)==primitive_weight(q,1)
    assert [primitive_weight(5,n) for n in range(5)]==[0,3,-1,-1,-1]
    assert all(primitive_weight(6,n)==0 for n in range(6))
    print(f'Exact primitive weight tests: {total} residue classes, q=1,...,36; independent character enumeration and cyclotomic reduction passed.')


def prime_powers(N):
    isp=bytearray(b'\x01')*(N+1); isp[:2]=b'\x00\x00'
    for p in range(2,isqrt(N)+1):
        if isp[p]: isp[p*p:N+1:p]=b'\x00'*((N-p*p)//p+1)
    out=[]
    for p in range(2,N+1):
        if isp[p]:
            k=p
            while k<=N:
                out.append((k,log(p)))
                k*=p
    return sorted(out)


def sample():
    xs=[10,30,100,300,1000,3000,10000]
    r=Q(2); pp=prime_powers(8*max(xs))
    path=Path(__file__).with_name('sample_values.csv')
    with path.open('w',newline='') as f:
        w=csv.writer(f); w.writerow(['family','q','r','x','G','G_over_sqrt_x'])
        for q in [1,5,6,8,11]:
            for kind in ['all_mod_q','primitive_conductor_q']:
                a=(lambda n: int((n-1)%q==0)) if kind=='all_mod_q' else (lambda n: primitive_weight(q,n))
                for x in xs:
                    G=fsum(v*a(n)*float(kernel(r,Q(n,x))) for n,v in pp if x<n<8*x)
                    # Compare with the original four ramps, including past terms.
                    S=lambda y: fsum(v*a(n)*(1/n-1/y) for n,v in pp if n<=y)
                    other=x*fsum(float(c)*S(int(r**j*x)) for j,c in enumerate(coeff(r)))
                    assert abs(G-other)<1e-8*max(1,x),(q,x,G,other)
                    w.writerow([kind,q,str(r),x,f'{G:.12g}',f'{G/sqrt(x):.12g}'])
    print(f'Prime examples: {2*5*len(xs)} rows written to {path.name}; floating-point comparison of local and four-ramp forms passed.')

if __name__=='__main__':
    test_filter(); test_primitive(); sample()
