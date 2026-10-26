#!/usr/bin/env python3
"""Independent finite controls for the even-frame one-square center lemma.

These controls are not a proof of the unbounded theorem. They use direct
finite-ring order enumeration and square-residue enumeration.
"""
import json
from math import gcd
from pathlib import Path

def mul(a,b,d,m):
    return ((a[0]*b[0]+d*a[1]*b[1])%m,(a[0]*b[1]+a[1]*b[0])%m)

def power(a,k,d,m):
    z=(1%m,0)
    while k:
        if k&1: z=mul(z,a,d,m)
        a=mul(a,a,d,m);k//=2
    return z

def order(a,d,m):
    z=(1,0)
    for n in range(1,1000000):
        z=mul(z,a,d,m)
        if z==(1,0): return n
    raise RuntimeError('unexpectedly large finite control')

def radical(m):
    z=1;p=2
    while p*p<=m:
        if m%p==0:
            z*=p
            while m%p==0:m//=p
        p+=1
    return z*m

def check():
    moduli=[3,5,7,9,11,13,17,19,23,25,27,29,31,37,41,43,49,81,121,125,169,243,343,15,21,35,45,63,75,105,135,175,189,225]
    cases=0;frames=0;ramified=0
    for W in range(2,25,2):
        d=W*(W+2);e=(W+1,1)
        for M in moduli:
            ordw=order(power(e,W,d,M),d,M)
            k=ordw
            while k%2==0:k//=2
            L,Y=power(e,W*k,d,M)
            if power((L,Y),ordw//k,d,M)!=(1,0):raise ValueError('order')
            if power(e,W*k,d,2*W)[1]!=W:raise ValueError('frame parity')
            squares={u*u%M for u in range(M)}
            for j in range(5):
                q=radical(M)*(2*j+1)
                n=q+1
                if gcd(2*n,M)!=1:raise ValueError('unit')
                a0=(n*n+1)*pow(2*n,-1,M)%M
                target=(a0-L*L)*pow(2,-1,M)%M
                if target not in squares:raise ValueError((W,M,k,q,L,target))
                cases+=1
            if gcd(d,M)>1:ramified+=1
            frames+=1
    # Removing the even-W premise need not work. Find an entire odd-index
    # orbit obstruction modulo a prime, not only failure of the selected k.
    obstruction=None
    primes=[p for p in range(3,100,2) if all(p%d for d in range(2,int(p**.5)+1))]
    for W in range(3,20,2):
        d=W*(W+2);e=(W+1,1)
        for p in primes:
            ordw=order(power(e,W,d,p),d,p)
            ss={u*u%p for u in range(p)}
            if all(((1-power(e,W*k,d,p)[0]**2)*pow(2,-1,p))%p not in ss for k in range(1,2*ordw,2)):
                obstruction={'W':W,'q':p,'M':p,'order_of_e_to_W':ordw,'all_odd_k_checked_modulo':2*ordw}
                break
        if obstruction:break
    if obstruction is None:raise ValueError('no expected odd-frame obstruction')
    return {'status':'pass','frames':frames,'center_residue_cases':cases,'ramified_frames':ramified,'odd_frame_obstruction':obstruction,'scope':'Exact finite controls only; see independent review for the unbounded proof.'}

if __name__=='__main__':
    result=check();print(json.dumps(result,indent=2))
