#!/usr/bin/env python3
"""Independent bounded pair-interval and recurrence audit; no huge witnesses."""
import hashlib,json,math,sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:raise SystemExit('requires -I -S without -O')
base=Path(__file__).resolve().parents[2]
p=base/'research/p64-qcube75-q2-symbolic-full-zero'
pins={'README.md':'e21d63a0c11076bf0dbf4ae184a7366af72691e164ac63a99f9213243623f73e','check.py':'92aacacce6695a8169a329a93fae6d5e4ef09fad6a1b092cc26cc197ea01a2c7','result.json':'97e51a2b8b32566c1321bc776f4639ce63bafb16e5c9d702417d1f901b14c6e6'}
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
lo=powpair(74,1,181843,5475,False);hi=powpair(74,1,181843,5475,True)
klo=powpair(1945,2,109930,972*973,False);khi=powpair(1945,2,109930,972*973,True)
if not less((18*khi[1],khi[2]),(lo[1],lo[2])):raise RuntimeError('lower ratio failed')
if not less((hi[1],hi[2]),(19*klo[1],klo[2])):raise RuntimeError('upper ratio failed')
def matmul(A,B,m):return tuple(sum(A[2*i+k]*B[2*k+j] for k in range(2))%m for i in range(2) for j in range(2))
def matpow(A,n,m):
    r=(1,0,0,1)
    while n:
        if n&1:r=matmul(r,A,m)
        A=matmul(A,A,m);n//=2
    return r
g,_,c,_=matpow((74,5475,1,74),181843,291)
d=(g-3-72*c)%291
if (g,c,d,math.gcd(324,291))!=(131,88,194,3):raise RuntimeError('main modulus mismatch')
if d%97:raise RuntimeError('main division not exact')
Amod=(108*(d//97))%324
_,_,kmod,_=matpow((1945,972*973*2,2,1945),109930,324)
if (Amod,kmod,181843%324)!=(216,188,79) or (kmod-1+Amod-181843)%324:raise RuntimeError('gamma modulus mismatch')
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
print(json.dumps({'status':'PASS_BOUNDED_CHECKS','interval_bits':B,'strict_ratio':'18 < c/k < 19','main_mod_H':[g,c],'d_mod_H':d,'A_mod_U':Amod,'k_mod_U':kmod,'chebyshev_finite_cases':count,'source_pins':pins,'scope':'Independent pair intervals, modular matrices and finite Chebyshev checks; symbolic proof is separately reviewed, no gigantic strong or auxiliary coordinate expanded.'},sort_keys=True))
