#!/usr/bin/env python3
"""Independent bounded pair-interval and recurrence audit; no huge witnesses."""
import hashlib,json,math,sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:raise SystemExit('requires -I -S without -O')
base=Path(__file__).resolve().parents[2]
p=base/'research/p64-free-x75-symbolic-full-zero'
pins={'README.md':'55b8461349833e654768451e4e1f1eba0862412c539b933e6282345ee622bbd1','check.py':'ffb4100234a0ff058948198a307b2eb1f4b39bea35dea326bd048c4604f9c0ca','result.json':'a61d203637a4b0eeebe25c9df3a91ab9fbeb2574beb8987e922d8acabc2b9c0f'}
for f,h in pins.items():
    if hashlib.sha256((p/f).read_bytes()).hexdigest()!=h:raise RuntimeError('input hash mismatch: '+f)
B=384
def mul(A,B1,d,up):
    (a,b,e),(c,f,h)=A,B1
    x,y=a*c+d*b*f,a*f+b*c
    shift=max(0,max(x.bit_length(),y.bit_length())-B)
    if shift:
        q=(1<<shift)-1 if up else 0
        x,y=(x+q)>>shift,(y+q)>>shift
    return x,y,e+h+shift
def powpair(x,y,n,d,up):
    acc=(1,0,0);p=(x,y,0)
    while n:
        if n&1:acc=mul(acc,p,d,up)
        n//=2
        if n:p=mul(p,p,d,up)
    return acc
def less(a,b):
    x,e=a;y,f=b
    if abs(e-f)>10000:raise RuntimeError('comparison resource guard')
    return (x<<(max(0,e-f))) < (y<<(max(0,f-e)))
lo=powpair(245,1,226443,60024,False);hi=powpair(245,1,226443,60024,True)
klo=powpair(11665,2,139466,5832*5833,False);khi=powpair(11665,2,139466,5832*5833,True)
if not less((27*khi[1],khi[2]),(lo[1],lo[2])):raise RuntimeError('lower ratio failed')
if not less((hi[1],hi[2]),(28*klo[1],klo[2])):raise RuntimeError('upper ratio failed')
def matmul(A,B,m):return tuple(sum(A[2*i+k]*B[2*k+j] for k in range(2))%m for i in range(2) for j in range(2))
def matpow(A,n,m):
    r=(1,0,0,1)
    while n:
        if n&1:r=matmul(r,A,m)
        A=matmul(A,A,m);n//=2
    return r
g,_,c,_=matpow((245,60024,1,245),226443,975)
d=(g-8-243*c)%975
if (g,c,d,math.gcd(729,975))!=(65,249,0,3):raise RuntimeError('main modulus mismatch')
if d%325:raise RuntimeError('main division not exact')
Amod=(243*(d//325))%729
_,_,kmod,_=matpow((11665,5832*5833*2,2,11665),139466,729)
if (Amod,kmod,226443%729)!=(0,454,453) or (kmod-1+Amod-226443)%729:raise RuntimeError('gamma modulus mismatch')
# Independently check the odd Chebyshev identity at small residues. This is
# a sanity control, not a substitute for the universal recurrence proof.
count=0
for mod in range(2,33):
    for n in range(mod):
        z=(1-n*n)%mod
        s0,s1=1,(4*z-3)%mod  # T_1(x)/x and T_3(x)/x
        u0,u1=1,(4*n*n-1)%mod # U_0(n), U_2(n)
        for r in range(1,16):
            if s1!=((-1)**r*u1)%mod:raise RuntimeError('Chebyshev check')
            s0,s1=s1,((4*z-2)*s1-s0)%mod
            u0,u1=u1,((4*n*n-2)*u1-u0)%mod
            count+=1
print(json.dumps({'status':'PASS_BOUNDED_CHECKS','interval_bits':B,'strict_ratio':'27 < c/k < 28','main_mod_H':[g,c],'d_mod_H':d,'A_mod_U':Amod,'k_mod_U':kmod,'chebyshev_finite_cases':count,'source_pins':pins,'scope':'Independent pair intervals, modular matrices and finite Chebyshev checks; symbolic proof is separately reviewed, no gigantic strong or auxiliary coordinate expanded.'},sort_keys=True))
