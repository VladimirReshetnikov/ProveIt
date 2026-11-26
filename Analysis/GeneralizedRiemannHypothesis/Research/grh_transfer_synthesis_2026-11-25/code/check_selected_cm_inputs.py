#!/usr/bin/env python3
"""Independent exact checks of selected CM inputs, not full classification.

Requires only Python 3's standard library. Reads the two bundled JSON data
files beside this archive's provenance README. Does not import or execute
code from the earlier report. Paths are relative to this script, so the
working directory is immaterial. Write a fresh JSON certificate with:

    python3 code/check_selected_cm_inputs.py > validation/selected_cm_inputs.json

The supplied polynomial coefficients are treated as input data; their
identification with actual CM class polynomials is not established here.
Run without Python's -O option, because the checks use assertions.
"""
from pathlib import Path
from fractions import Fraction as Q
from math import comb, gcd, isqrt
import json

ROOT=Path(__file__).resolve().parents[1]
BASE=ROOT/'prior/cm_inputs'
data=json.loads((BASE/'five_small_witnesses.json').read_text())

def vp(n,p):
    if n==0:return 10**100
    r=0
    while n%p==0:r+=1;n//=p
    return r

def factv(n,p):
    s=0
    while n:
        n//=p;s+=n
    return s

disk=[]; forms=0
for Ds, entry in data.items():
    D=int(Ds)
    for a,b,c in entry.get('forms',[]):
        assert b*b-4*a*c==-D
        assert gcd(gcd(a,b),c)==1 and abs(b)<=a<=c
        forms+=1
    if 'disk' not in entry:continue
    p,a,u,ls,expected=entry['disk']; lam=Q(ls)
    H=entry['coefficients']; degree=len(H)-1
    B=[sum(H[j]*p**(a*j)*comb(j,i)*u**(j-i) for j in range(i,degree+1)) for i in range(degree+1)]
    val=[Q(vp(B[i],p))+i*lam for i in range(degree+1)]
    count=val.index(min(val))
    assert count==expected and count>=5
    assert lam>Q(1,p-1)
    cutoff=max(i*lam-factv(i,p) for i in range(5))
    # For n past N, n*(lam-1/(p-1)) > cutoff, so factorial bound settles all.
    N=max(5,int(cutoff/(lam-Q(1,p-1)))+2)
    bad=[n for n in range(5,N+1) if n*lam-factv(n,p)<=cutoff]
    assert len(bad)==0
    disk.append({'D':D,'p':p,'depth':str(lam),'roots':count,'fewnomial_max_roots':4})

all_polys=json.loads((BASE/'class_polynomials.json').read_text())
def mulmod(a,b,H,mod):
    d=len(H)-1
    c=[0]*(2*d-1)
    for i,ai in enumerate(a):
        for j,bj in enumerate(b):c[i+j]=(c[i+j]+ai*bj)%mod
    for k in range(2*d-2,d-1,-1):
        v=c[k]
        for j in range(d):c[k-d+j]=(c[k-d+j]-v*H[j])%mod
    return c[:d]
def xpower(m,H,mod):
    d=len(H)-1
    a=[0]*d;a[1]=1
    b=[0]*d;b[0]=1
    while m:
        if m&1:b=mulmod(a,b,H,mod)
        a=mulmod(a,a,H,mod);m//=2
    return b
params={131:[(601,200),(1051,350),(4201,1400),(6301,1050),(757,252),(337,112)],
        87:[(103,102),(1531,1530),(151,150),(487,486),(1459,486)],
        348:[(487,486),(1459,486)],432:[(109,36),(433,144)],675:[(241,40),(13,56)]}
periods=[]
for D,pairs in params.items():
    H=all_polys['-131'] if D==131 else data[str(D)]['coefficients']
    for p,m in pairs:
        assert p>6 and all(p%k for k in range(2,isqrt(p)+1))
        v=xpower(m,H,p*p)
        assert v[0]%p and all(x%p==0 for x in v[1:])
        periods.append({'D':D,'p':p,'m':m,'a_mod_p_squared':v[0],'D_mod_p':[0]+[x//p for x in v[1:]]})
result={'checked_newton_disks':disk,'checked_reduced_forms':forms,'checked_confluent_periods':periods,
        'scope':'Independent exact checks of 18 Newton disk certificates, 245 reduced-form discriminants and 17 confluent period identities only. Class-polynomial identity, analytic enclosures, large finite residue sieves and global completeness not replayed.'}
assert (len(disk), forms, len(periods)) == (18, 245, 17)
result['status']='passed'
result['counts']={'newton_disks':len(disk),'reduced_forms':forms,'confluent_period_identities':len(periods)}
print(json.dumps(result,indent=2))
