#!/usr/bin/env python3
"""Independent bounded pair-interval and recurrence audit; no huge witnesses."""
import hashlib,json,math,sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:raise SystemExit('requires -I -S without -O')
base=Path(__file__).resolve().parents[2]
p=base/'research/p64-free-fsquare75-symbolic-full-zero'
pins={'README.md':'04f4463f12dd173f0360b1eb64bd7081f69a2e362a5eaadfbb1fa79e1dfb5b3b','check.py':'fe7159ca3efbd0fa922ea46a66157d192f63185691c4599f31fc40b955f2cbf4','result.json':'f34ccd14e96ee665ddac13c7d8c64c65e547064fcb6fe390a4df61713ba9284f'}
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
lo=powpair(191,1,4020619,36480,False);hi=powpair(191,1,4020619,36480,True)
klo=powpair(8749,2,2446738,4374*4375,False);khi=powpair(8749,2,2446738,4374*4375,True)
if not less((27*khi[1],khi[2]),(lo[1],lo[2])):raise RuntimeError('lower ratio failed')
if not less((hi[1],hi[2]),(28*klo[1],klo[2])):raise RuntimeError('upper ratio failed')
def matmul(A,B,m):return tuple(sum(A[2*i+k]*B[2*k+j] for k in range(2))%m for i in range(2) for j in range(2))
def matpow(A,n,m):
    r=(1,0,0,1)
    while n:
        if n&1:r=matmul(r,A,m)
        A=matmul(A,A,m);n//=2
    return r
g,_,c,_=matpow((191,36480,1,191),4020619,759)
d=(g-6-189*c)%759
if (g,c,d,math.gcd(729,759))!=(488,538,506,3):raise RuntimeError('main modulus mismatch')
if d%253:raise RuntimeError('main division not exact')
Amod=(243*(d//253))%729
_,_,kmod,_=matpow((8749,4374*4375*2,2,8749),2446738,729)
if (Amod,kmod,4020619%729)!=(486,428,184) or (kmod-1+Amod-4020619)%729:raise RuntimeError('gamma modulus mismatch')
_,_,c31,_=matpow((191,36480,1,191),4020619,31)
f2=(1+36480*pow(c31,4,31))%31
squares={x*x%31 for x in range(31)}
if c31!=29 or f2!=13 or f2 in squares:raise RuntimeError('nonsquare check')
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
print(json.dumps({'status':'PASS_BOUNDED_CHECKS','interval_bits':B,'strict_ratio':'27 < c/k < 28','main_mod_H':[g,c],'d_mod_H':d,'A_mod_U':Amod,'k_mod_U':kmod,'c_mod_31':c31,'F2_mod_31':f2,'squares_mod_31':sorted(squares),'chebyshev_finite_cases':count,'source_pins':pins,'scope':'Independent pair intervals, modular matrices and finite Chebyshev checks; symbolic proof is separately reviewed, no gigantic strong or auxiliary coordinate expanded.'},sort_keys=True))
