#!/usr/bin/env python3
"""Independent literal-polynomial audit: no import from the builder or verifier."""
import json
from math import comb
from pathlib import Path

def require(value, message):
    if not value:
        raise RuntimeError(message)


def add(*ps):
    r={}
    for p in ps:
        for m,c in p.items():r[m]=r.get(m,0)+c
    return {m:c for m,c in r.items() if c}
def scale(p,a):return {m:c*a for m,c in p.items() if c*a}
def mul(p,q):
    r={}
    for (a,b,c),v in p.items():
        for (d,e,f),w in q.items():
            m=(a+d,b+e,c+f);r[m]=r.get(m,0)+v*w
    return {m:c for m,c in r.items() if c}
def power(p,n):
    r={(0,0,0):1}
    for k in range(n):r=mul(r,p)
    return r
def subtract(p,q):return add(p,scale(q,-1))
def lit(x):return {(0,0,0):x} if x else {}
def product(*ps):
    r=lit(1)
    for p in ps:r=mul(r,p)
    return r
A={(1,0,0):1};C={(0,1,0):1};i={(0,0,1):1}
D=add(product(A,A,C,C),scale(product(C,C),-1),lit(1))
e=product(i,add(scale(A,4),lit(-5)),C)
L=add(product(C,D),lit(1),scale(A,-1))
F=add(product(e,e,D,D,add(D,lit(-1))),lit(1))
G=add(A,product(F,L))
Ns=add(scale(G,2),L)
N1=add(scale(product(e,e,D,add(D,lit(-1)),L),2),scale(C,3))
N2=scale(product(e,e,add(D,lit(-1)),L),2)
N3=scale(product(e,e,subtract(L,C)),2)
N4=scale(product(e,e,C),2)
corr=add(product(i,i,e,add(lit(560),scale(add(A,lit(-1),scale(C,-3)),-224))),scale(i,320),lit(2048))
T6=add(product(e,add(product(add(scale(power(D,2),1024),scale(D,-512),lit(-128)),Ns),scale(N1,-64),scale(N2,-40),scale(N3,-28),scale(N4,-21))),corr)
T7=add(scale(T6,2),scale(product(i,i,e,C),-1056))
# Compare the folded builder expression to the literal T7.
folded=add(product(e,add(product(add(scale(power(D,2),2048),scale(D,-1024),lit(-256)),Ns),scale(N1,-128),scale(N2,-80),scale(N3,-56),scale(N4,-42),product(i,i,add(lit(1568),scale(A,-448),scale(C,288))))),scale(i,640),lit(4096))
require(T7==folded, 'T7 literal folding identity')
coeffs={7:2048,6:-1024,5:-256,4:-128,3:-80,2:-56,1:-42,0:-33}
tn=add(*(scale(power(D,k),v) for k,v in coeffs.items()))
remainder=add(product(power(D,5),T7),scale(product(e,tn,Ns),-1),scale(power(D,5),-4096))
shift={}
for (a,c,j),v in remainder.items():
    for aa in range(a+1):
        for cc in range(c+1):
            mon=(aa,cc,j)
            shift[mon]=shift.get(mon,0)+v*comb(a,aa)*3**(a-aa)*comb(c,cc)
shift={m:v for m,v in shift.items() if v}
cert=json.loads((Path(__file__).resolve().parent.parent / 'nine/data/order7_majorant_positive_certificate.json').read_text())
claimed={tuple(t['powers']):t['coefficient'] for t in cert['terms']}
require(shift==claimed, 'exact 264-term coefficient certificate')
require(len(shift)==264 and min(shift.values())>0, 'strict positivity of all 264 coefficients')
require(any(m[0]==m[1]==0 for m in shift), 'strict positive constant in shifted A,C')
print('Literal T7 identity and all 264 certificate coefficients independently verified.')
print('All coefficients strictly positive; minimum:',min(shift.values()))
print('Terms independent of A-3,C-1:',{str(m):v for m,v in shift.items() if m[0]==m[1]==0})
# A one-variable identity, using A only as a formal indeterminate.
tn1=add(*(scale(power(A,k),v) for k,v in coeffs.items()))
dn=add(power(tn1,2),scale(product(power(A,13),add(A,lit(-1))),-2048**2))
expected={6:109824,5:36608,4:18304,3:9984,2:5460,1:2772,0:1089}
require(dn=={(k,0,0):v for k,v in expected.items()}, 'exact tn7 square identity')
print('Exact tn7^2 - 2048^2 D^13(D-1) identity verified:',expected)
# tn is positive for D>=2: replace D=z+2 and inspect coefficient signs.
shift1={}
for (a,b,c),v in tn1.items():
    for aa in range(a+1):shift1[aa]=shift1.get(aa,0)+v*comb(a,aa)*2**(a-aa)
require(min(shift1.values())>0, 'tn7 positive for D>=2')
print('tn7 is strictly positive for every real D>=2 by coefficient expansion.')
# Ring identities for denominator clearing, with unrelated formal variables.
def gadd(*ps):
    z={}
    for p in ps:
        for m,c in p.items():z[m]=z.get(m,0)+c
    return {m:c for m,c in z.items() if c}
def gs(p,k):return {m:c*k for m,c in p.items() if c*k}
def gm(p,q):
    z={}
    for a,c in p.items():
        for b,d in q.items():
            m=tuple(x+y for x,y in zip(a,b));z[m]=z.get(m,0)+c*d
    return {m:c for m,c in z.items() if c}
def gc(n,v):return {(0,)*n:v} if v else {}
def gv(n,k):return {tuple(int(j==k) for j in range(n)):1}
def gp(p,k,n):
    z=gc(n,1)
    for _ in range(k):z=gm(z,p)
    return z
def gprod(n,*ps):
    z=gc(n,1)
    for p in ps:z=gm(z,p)
    return z
D,e,L,v,R=(gv(5,j) for j in range(5))
one=gc(5,1);dm1=gadd(D,gs(one,-1))
X=gprod(5,e,e,gp(D,3,5),dm1)
F=gadd(gprod(5,e,e,D,D,dm1),one)
G=gadd(gprod(5,gadd(F,gs(one,-1)),L),v)
Ns=gadd(gs(G,2),L)
tn=gadd(*(gs(gp(D,k,5),a) for k,a in coeffs.items()))
dn=gadd(*(gs(gp(D,k,5),a) for k,a in expected.items()))
left=gadd(gp(gadd(gprod(5,e,tn,Ns),R),2,5),gs(gprod(5,gp(D,11,5),F,G,G),-4096**2))
right=gadd(gprod(5,e,e,dn,Ns,Ns),gs(gprod(5,gp(D,10,5),gadd(gprod(5,X,L,L),gs(gprod(5,D,G,v),-4))),2048**2),gs(gprod(5,e,tn,Ns,R),2),gp(R,2,5))
require(left==right, 'formal D^10 majorant-defect identity')
print('D^10 majorant-defect identity verified in the formal ring Z[D,e,L,v,R].')
E,Om,V0,V1,a0,a1=(gv(6,j) for j in range(6))
d0=gadd(gp(V0,2,6),gs(a0,-1));d1=gadd(gp(V1,2,6),gs(a1,-1))
Th=gadd(E,gs(gm(Om,gadd(V0,V1)),-1))
F9=gadd(gp(gadd(gp(Th,2,6),gs(gprod(6,Om,Om,gadd(a0,a1)),-1)),2,6),gs(gprod(6,gp(Om,4,6),a0,a1),-4))
B=gadd(gp(E,2,6),gs(gprod(6,E,Om,gadd(V0,V1)),-2),gprod(6,Om,Om,gadd(d0,d1)))
F9b=gadd(gp(B,2,6),gs(gprod(6,Om,Om,V0,V1,B),4),gs(gprod(6,gp(Om,4,6),gadd(gprod(6,d0,V1,V1),gprod(6,a0,d1))),4))
require(F9==F9b, 'formal final two-defect identity')
print('Two-defect final-norm identity verified in six independent formal variables.')
weights=(18729,1,1)
wd=max(sum(x*y for x,y in zip(m,weights)) for m in remainder)
heads=[(m,c) for m,c in remainder.items() if sum(x*y for x,y in zip(m,weights))==wd]
require(wd==187305 and heads==[((10,12,3),2880)], 'unique weighted remainder leading term')
print('New remainder weighted leading term: 2880 A^10 C^12 i^3, degree 187305.')
