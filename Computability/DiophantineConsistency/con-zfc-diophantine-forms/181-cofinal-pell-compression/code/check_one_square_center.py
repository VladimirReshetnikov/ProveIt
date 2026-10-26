#!/usr/bin/env python3
"""Bounded independent checks for the cofinal one-scaled-square theorem.

No external dependencies. These checks corroborate the ordinary proof;
they cannot replace its unbounded quantifiers.
"""
import json
import math


def factors(n):
    out=[]
    p=2
    while p*p<=n:
        a=0
        while n%p==0:
            n//=p
            a+=1
        if a:
            out.append((p,a))
        p+=1
    if n>1:
        out.append((n,1))
    return out


def mul(x,y,D,m):
    return ((x[0]*y[0]+D*x[1]*y[1])%m,
            (x[0]*y[1]+x[1]*y[0])%m)


def power(x,n,D,m):
    y=(1%m,0)
    while n:
        if n&1:
            y=mul(y,x,D,m)
        x=mul(x,x,D,m)
        n//=2
    return y


def oddpart(n):
    while n%2==0:
        n//=2
    return n


def exponent_bound(W,M):
    """An exponent divisible by the order of every local norm-one unit."""
    D=W*(W+2)
    E=1
    for p,a in factors(M):
        chi=pow(D%p,(p-1)//2,p)
        if chi==0:
            local=2*p**a
        else:
            chi=1 if chi==1 else -1
            local=(p-chi)*p**(a-1)
        E=math.lcm(E,local)
    return E


def main():
    count=0
    max_k=0
    nontrivial=0
    for M in range(3,1000,2):
        fs=factors(M)
        rad=math.prod(p for p,a in fs)
        square_set={u*u%M for u in range(M)}
        for W in range(2,82,2):
            D=W*(W+2)
            e=(W+1,1)
            E=exponent_bound(W,M)
            if power(e,E,D,M)!=(1,0):
                raise ValueError(('bad exponent bound',W,M,E))
            k=oddpart(E)
            max_k=max(max_k,k)
            L,Y=power(e,W*k,D,M)
            if k%2!=1:
                raise ValueError('k is not odd')
            # Power-of-two order can be checked using the remaining 2 part.
            if power((L,Y),E//k,D,M)!=(1,0):
                raise ValueError(('not power-two order',W,M))
            # Verify directly in modulus 2W that the exact ordinate/W is odd.
            _,ypar=power(e,W*k,D,2*W)
            if ypar!=W:
                raise ValueError(('wrong frame quotient parity',W,M,k,ypar))
            for q in (rad,3*rad,5*rad):
                n=q+1
                a0=(n*n+1)*pow(2*n,-1,M)%M
                c=(a0-L*L)*pow(2,-1,M)%M
                if c not in square_set:
                    raise ValueError(('counterexample',W,q,M,k,L,c))
                count+=1
            for p,a in fs:
                if L%p not in (1,p-1):
                    nontrivial+=1
                    # Construct and check the elementary order-eight witness.
                    ep=(e[0]%p,e[1]%p)
                    order=1
                    cur=ep
                    while cur!=(1,0):
                        cur=mul(cur,ep,D,p)
                        order+=1
                        if order>2*p:
                            raise ValueError(('unexpected field order',W,p))
                    if order%8:
                        raise ValueError(('missing order eight',W,p,order))
                    H,Z=power(ep,order//8,D,p)
                    if (2*H*H-1)%p or ((D*Z)**2+D*pow(2,-1,p))%p:
                        raise ValueError(('order-eight identity failed',W,p))
    # Guard and scaling negative controls.
    odd_fail=[]
    for k in range(1,21,2):
        L,Y=power((6,1),5*k,35,3)
        odd_fail.append(all((L*L+2*u*u-1)%3 for u in range(3)))
    if not all(odd_fail):
        raise ValueError('odd-W negative control disappeared')
    square27={u*u%27 for u in range(27)}
    if 18 in square27 or (2*3*3)%27!=18:
        raise ValueError('scaling negative control failed')
    for k in range(1,21,2):
        L,Y=power((7,1),6*k,48,27)
        if L*L%27!=1:
            raise ValueError('unscaled-square frame control failed')
    print(json.dumps({
        'status':'passed',
        'even_W':{'first':2,'last':80},
        'odd_M':{'first':3,'last':999},
        'q_values':'rad(M), 3 rad(M), 5 rad(M)',
        'center_congruence_checks':count,
        'nontrivial_local_order8_checks':nontrivial,
        'largest_selected_odd_multiplier':max_k,
        'negative_controls':{'odd_W_5_q3_M3':'fails as required',
                             'unscaled_square_W6_q3_M27':'fails as required'},
        'scope':'bounded exact regressions; not an unbounded proof'
    },indent=2))


if __name__=='__main__':
    main()
