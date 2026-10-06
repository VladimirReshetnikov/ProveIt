#!/usr/bin/env python3
"""Bounded, exact independent checks for ordered symmetric packed matrices.

The all-order asymptotic theorem is proved in the article, not by this program.
No cache bypasses public validation. Large integers are recorded in binary hash
encodings, never converted to unbounded decimal strings.
"""
from __future__ import annotations
import sys
sys.dont_write_bytecode = True
import argparse
from collections import defaultdict
from fractions import Fraction
import hashlib
from math import comb, factorial
from common import emit, integer, new_file_path, require

MAX_N = 640
IE_MAX = 32
COLLISION_IE_MAX = 12
DIRECT_MAX = 6
A138178_PREFIX = (1,1,3,9,33,125,531,2349,11205,55589,291423,1583485,
    8985813,52661609,319898103,2000390153,12898434825,85374842121,
    580479540219,4041838056561,28824970996809,210092964771637,
    1564766851282299,11890096357039749,92151199272181629)


def ordered_bells(n, u=1):
    integer(n,0,MAX_N,'n'); integer(u,1,4,'dimension marker')
    out=[1]
    for m in range(1,n+1):
        out.append(u*sum(comb(m,j)*out[m-j] for j in range(1,m+1)))
    return tuple(out)


def involutions(n, V=1, D=1):
    """Return D^j I_j(V/D), 0<=j<=n, as exact integers."""
    integer(n,0,MAX_N,'n'); integer(V,0,4,'trace numerator'); integer(D,1,4,'trace denominator')
    out=[1]
    if n:out.append(V)
    for m in range(2,n+1):out.append(V*out[-1]+D*D*(m-1)*out[-2])
    return tuple(out)


def coefficient_polynomials(n, V=1, D=1):
    """Return Q_j(k)=D^j j! f_j(k,V/D), in ascending powers of k."""
    integer(n,0,MAX_N,'n'); integer(V,0,4,'trace numerator'); integer(D,1,4,'trace denominator')
    out=[(1,)]
    if n:out.append((0,V))
    def add(target,poly,mult,shift=0):
        for j,c in enumerate(poly):target[j+shift]+=mult*c
    for m in range(1,n):
        row=[0]*(m+2)
        add(row,out[m],V,1); add(row,out[m],V*m)
        add(row,out[m-1],m*D*D,2); add(row,out[m-1],-m*D*D,1)
        add(row,out[m-1],m*D*D*(m-1))
        if m>=2:
            add(row,out[m-2],-V*D*D*m*(m-1),2)
            add(row,out[m-2],-V*D*D*m*(m-1)*(m-2))
        out.append(tuple(row))
    return tuple(out)


def recurrence_counts(n, u=1, V=1, D=1):
    integer(n,0,MAX_N,'n'); integer(u,1,4,'dimension marker')
    integer(V,0,4,'trace numerator'); integer(D,1,4,'trace denominator')
    bells=ordered_bells(n,u); polys=coefficient_polynomials(n,V,D)
    return tuple(Fraction(sum(c*bells[j] for j,c in enumerate(poly)),factorial(m)*D**m)
                 for m,poly in enumerate(polys))


def _multiset(cells, units):
    return int(units==0) if cells==0 else comb(cells+units-1,units)


def _coefficient(n,k,v,binary=False):
    pairs=k*(k-1)//2
    return sum((Fraction(comb(k,t)*comb(pairs,(n-t)//2)) if binary
                and t<=k and (n-t)//2<=pairs else Fraction(0)) * v**t
               if binary else Fraction(_multiset(k,t)*_multiset(pairs,(n-t)//2))*v**t
               for t in range(n%2,n+1,2))


def deletion_count(n,u=1,V=1,D=1,binary=False):
    """Independent stars-and-bars/binomial counts followed by zero-line deletion."""
    integer(n,0,IE_MAX,'n'); integer(u,1,4,'dimension marker')
    integer(V,0,4,'trace numerator'); integer(D,1,4,'trace denominator')
    require(type(binary) is bool,'binary must be a boolean')
    v=Fraction(V,D)
    f=[_coefficient(n,k,v,binary) for k in range(n+1)]
    return sum(u**d*sum((-1)**(d-k)*comb(d,k)*f[k] for k in range(d+1)) for d in range(n+1))


def collision_marked_count(n,u=1,V=1,D=1,w=1,zeta=1):
    """Independent exact numerator-factor expansion of collision markers."""
    integer(n,0,COLLISION_IE_MAX,'n'); integer(u,1,4,'dimension marker')
    integer(V,0,4,'trace numerator'); integer(D,1,4,'trace denominator')
    integer(w,0,3,'diagonal collision marker'); integer(zeta,0,3,'off-diagonal collision marker')
    v=Fraction(V,D); f=[]
    for k in range(n+1):
        pairs=k*(k-1)//2; value=Fraction(0)
        for r in range(min(k,n//2)+1):
            for s in range(min(pairs,(n-2*r)//4)+1):
                value+=comb(k,r)*comb(pairs,s)*(w-1)**r*(zeta-1)**s*v**(2*r)*_coefficient(n-2*r-4*s,k,v)
        f.append(value)
    return sum(u**d*sum((-1)**(d-k)*comb(d,k)*f[k] for k in range(d+1)) for d in range(n+1))


def direct_distribution(n):
    """Enumerate actual upper-triangle entries; key is (dimension, trace, R, S)."""
    integer(n,0,DIRECT_MAX,'n')
    if n==0:return {(0,0,0,0):1}
    result=defaultdict(int)
    for d in range(1,n+1):
        cells=[(i,j) for i in range(d) for j in range(i,d)]
        full=(1<<d)-1
        def visit(index,left,mask,trace,r,s):
            if d-mask.bit_count()>left:return
            if left==0:
                if mask==full:result[(d,trace,r,s)]+=1
                return
            if index==len(cells):return
            i,j=cells[index]; diagonal=i==j; cost=1 if diagonal else 2
            visit(index+1,left,mask,trace,r,s)
            for value in range(1,left//cost+1):
                visit(index+1,left-cost*value,mask|(1<<i)|(1<<j),
                      trace+(value if diagonal else 0),r+int(diagonal and value>=2),
                      s+int(not diagonal and value>=2))
        visit(0,n,0,0,0,0)
    return dict(sorted(result.items()))


def collision_moments(n):
    """Exact rational factorial moments E[R], E[S], E[(R)2], E[(S)2], E[RS]."""
    integer(n,0,MAX_N,'n')
    polys=coefficient_polynomials(n); bells=ordered_bells(n)
    total=sum(c*bells[j] for j,c in enumerate(polys[n]))
    def moment(loss,shifts,denominator):
        if n<loss:return Fraction(0)
        value=sum(c*sum(a*bells[j+s] for s,a in shifts) for j,c in enumerate(polys[n-loss]))
        return Fraction(factorial(n)//factorial(n-loss)*value,denominator*total)
    er=moment(2,((1,1),),1)
    es=moment(4,((2,1),(1,-1)),2)
    rr=moment(4,((2,1),(1,-1)),1)
    ss=moment(8,((4,1),(3,-2),(2,-1),(1,2)),4)
    rs=moment(6,((3,1),(2,-1)),2)
    return {'E_R':er,'E_S':es,'E_R_falling_2':rr,'E_S_falling_2':ss,'E_RS':rs}


def collision_moments_deletion(n):
    """Independent factorial moments from marked cells followed by zero-line deletion."""
    integer(n,0,COLLISION_IE_MAX,'n')
    total=deletion_count(n)
    def raw(r,s):
        loss=2*r+4*s
        if n<loss:return Fraction(0)
        f=[]
        for k in range(n+1):
            pairs=k*(k-1)//2
            choices=(factorial(k)//factorial(k-r) if k>=r else 0)
            choices*=factorial(pairs)//factorial(pairs-s) if pairs>=s else 0
            f.append(choices*_coefficient(n-loss,k,Fraction(1)))
        return sum(sum((-1)**(d-k)*comb(d,k)*f[k] for k in range(d+1)) for d in range(n+1))/total
    return {key:raw(r,s) for key,r,s in (('E_R',1,0),('E_S',0,1),
            ('E_R_falling_2',2,0),('E_S_falling_2',0,2),('E_RS',1,1))}


def integer_digest(values):
    """SHA256 of length-prefixed signed big-endian magnitudes (no decimal conversion)."""
    require(isinstance(values,(tuple,list)) and len(values)<=MAX_N+1,'invalid hash sequence')
    require(all(type(x) is int and x.bit_length()<=100000 for x in values),'invalid hash integer')
    h=hashlib.sha256()
    for value in values:
        raw=abs(value).to_bytes(max(1,(abs(value).bit_length()+7)//8),'big')
        h.update(bytes([int(value<0)]));h.update(len(raw).to_bytes(4,'big'));h.update(raw)
    return h.hexdigest()


def verify(n=640):
    integer(n,24,MAX_N,'verification n')
    counts=recurrence_counts(n)
    require(all(x.denominator==1 and x>=0 for x in counts),'integrality or positivity failure')
    integers=tuple(x.numerator for x in counts)
    require(integers[:len(A138178_PREFIX)]==A138178_PREFIX,'A138178 published prefix mismatch')
    checks=[]
    for m in range(IE_MAX+1):
        require(deletion_count(m)==integers[m] if m<=n else deletion_count(m)==recurrence_counts(m)[-1],
                'independent deletion mismatch')
    checks.append('unmarked recurrence versus independent deletion for n=0..32')
    for u,V,D in ((1,0,1),(1,1,2),(2,2,1),(3,3,2)):
        marked=recurrence_counts(16,u,V,D)
        for m in range(17):require(marked[m]==deletion_count(m,u,V,D),'marked deletion mismatch')
    checks.append('dimension/trace marked identities for n=0..16 at four rational marker pairs')
    binary=[]
    for m in range(COLLISION_IE_MAX+1):
        b=deletion_count(m,binary=True); require(b.denominator==1,'binary integrality')
        binary.append(b.numerator)
        require(collision_marked_count(m,w=0,zeta=0)==b,'zero collision markers are not binary')
        require(collision_marked_count(m)==integers[m],'unit collision markers mismatch')
    require(binary==[1,1,2,6,20,74,302,1314,6122,29982,154718,831986,4667070],
            'A135588 published prefix mismatch')
    for m in range(COLLISION_IE_MAX+1):
        require(collision_moments(m)==collision_moments_deletion(m),'independent collision-moment deletion mismatch')
    checks.append('collision factorial moments versus independent marked-cell deletion through n=12')
    for m in range(DIRECT_MAX+1):
        dist=direct_distribution(m)
        require(sum(dist.values())==integers[m],'direct enumeration mismatch')
        require(sum(c for (d,t,r,s),c in dist.items() if r==s==0)==binary[m],'direct binary mismatch')
        for u,V,D,w,zeta in ((2,1,2,3,2),(1,2,1,0,3),(3,3,2,2,0)):
            value=sum(c*u**d*Fraction(V,D)**t*w**r*zeta**s for (d,t,r,s),c in dist.items())
            require(value==collision_marked_count(m,u,V,D,w,zeta),'direct fully marked mismatch')
        numerators={key:0 for key in collision_moments(m)}
        for (d,t,r,s),c in dist.items():
            for key,value in zip(numerators,(r,s,r*(r-1),s*(s-1),r*s)):numerators[key]+=c*value
        require(collision_moments(m)=={key:Fraction(value,integers[m]) for key,value in numerators.items()},
                'collision moments versus direct enumeration mismatch')
        require(all((m-t)%2==0 for d,t,r,s in dist),'trace parity failure')
    checks.extend(('direct matrix enumeration and joint markers through n=6',
                   'collision factorial moments versus direct enumeration through n=6',
                   'binary collision specialization versus independent binomial deletion through n=12'))
    for V,D in ((1,1),(1,2),(0,1),(3,2)):
        inv=involutions(n,V,D)
        for m in range(n+1):
            direct=sum(factorial(m)//(factorial(m-2*j)*2**j*factorial(j))*V**(m-2*j)*D**(2*j)
                       for j in range(m//2+1))
            require(inv[m]==direct,'involution recurrence versus explicit sum mismatch')
    checks.append('involution recurrence versus factorial sum at four trace markers through requested n')
    return {'status':'PASS','scope':'Bounded exact arithmetic checks; not a proof of asymptotic remainders',
            'n':n,'hard_workload_cap':MAX_N,'A138178_prefix':list(A138178_PREFIX),
            'binary_prefix_n0_to12':binary,'checks':checks,'count_binary_sha256':integer_digest(integers),
            'last_count_bit_length':integers[-1].bit_length(),
            'involution_binary_sha256':integer_digest(involutions(n)),
            'integer_decimal_digit_cap':sys.get_int_max_str_digits()}


def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--n',type=int,default=640);p.add_argument('--output')
    a=p.parse_args()
    if a.output is not None:new_file_path(a.output)
    emit(verify(a.n),a.output)

if __name__=='__main__':
    try:main()
    except (ValueError,RuntimeError,OSError,ArithmeticError) as exc:raise SystemExit(str(exc))
