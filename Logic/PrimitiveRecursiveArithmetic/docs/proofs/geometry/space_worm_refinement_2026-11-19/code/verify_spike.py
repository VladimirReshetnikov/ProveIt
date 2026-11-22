"""Rational verification for a one-point extension of a one-sided lift.

Run with Python 3.8 or later. Only fractions and integer square roots are used.
"""
from fractions import Fraction as F
from math import isqrt

PARAMETERS = (F(-631,58), F(-1), F(7,16), F(37,56))
OFFSETS = (F(0), F(0), F(130783,250000), F(446199,1000000))
NORMALS = [((1-t*t)/(1+t*t), 2*t/(1+t*t)) for t in PARAMETERS]

def det(u,v):
    return u[0]*v[1]-u[1]*v[0]

def intersection(i,j):
    a,b = NORMALS[i]
    c,d = NORMALS[j]
    return ((OFFSETS[i]*d-b*OFFSETS[j])/det(NORMALS[i],NORMALS[j]),
            (a*OFFSETS[j]-OFFSETS[i]*c)/det(NORMALS[i],NORMALS[j]))

def sqrt_upper(q):
    """Upper bound with absolute excess at most 10^-13."""
    precision = 10**13
    numerator = q.numerator * precision**2
    lower = isqrt(numerator // q.denominator)
    if lower**2*q.denominator == numerator:
        return F(lower,precision)
    return F(lower+1,precision)

verts = [intersection(i,(i+1)%4) for i in range(4)]
assert all(a*x+b*y <= d for (a,b),d in zip(NORMALS,OFFSETS)
           for x,y in verts)
assert verts[0] == (0,0)
xmin,Y = verts[3]
assert xmin == min(x for x,y in verts)
assert Y == max(y for x,y in verts) and min(y for x,y in verts)==0
area = sum(det(u,v) for u,v in zip(verts,verts[1:]+verts[:1]))/2
H2 = Y**2 / (1+9*Y**2)
Hhi = sqrt_upper(H2)
T = 1/Y
assert 9*H2<1

assert all(nx <= 0 and ny <= 0 for nx,ny in NORMALS[:2])
assert all(nx > 0 and ny > 0 for nx,ny in NORMALS[2:])
table = {(2,0): "-1.91", (2,1): "-0.014", (2,2): "-0.60", (2,3): "-0.44",
         (3,0): "-0.93", (3,1): "-0.055", (3,2): "-0.18"}
for i in (2,3):
    a,b = NORMALS[i]
    d = OFFSETS[i]
    for j,(x,y) in enumerate(verts):
        if (i,j)==(3,3):
            continue
        X = x-xmin
        A = (a*X)**2 + 9*d*d*y*y - d*d
        B = 2*a*X*b
        C = b*b-9*d*d
        candidates = [0,T]
        if A<0 and 0<-B/(2*A)<T:
            candidates.append(-B/(2*A))
        assert max(A*t*t+B*t+C for t in candidates) <= F(table[i,j])

a,b = NORMALS[3]
d = OFFSETS[3]
m = d/b
assert all(ny*m<=di for (nx,ny),di in zip(NORMALS,OFFSETS))
assert Hhi*(1+1/(9*Y**2)) <= m
# All normals other than side 3 admit E at height H.
assert all(ny*Hhi<=0 or ny**2*H2 <= di**2*(1-9*H2)
           for (nx,ny),di in zip(NORMALS[:3],OFFSETS[:3]))

Lhi = sqrt_upper(sum((x-y)**2 for x,y in zip(verts[2],verts[3])))
# Concavity gives a lower chord on each interval. A bound M on -g''
# limits the excess of g above that chord to M/(8*n*n). The positive
# part is 1-Lipschitz. All quantities below are rational enclosures.
def sqrt_lower(q):
    precision = 10**15
    return F(isqrt((q.numerator * precision**2) // q.denominator),precision)

def positive_chord_mean(u,v):
    if u <= 0 and v <= 0:
        return F(0)
    if u >= 0 and v >= 0:
        return (u+v)/2
    return max(u,v)**2/(2*abs(v-u))

n = 8192
# g(v)=b*H*sqrt(1-9H²v²)-d*(1-9H²v).
# Since H<1/3, b<1 and 1-9H²>1/4, one has -g''<8/3<3.
assert H2 < F(1,9) and 0<b<1 and 1-9*H2>F(1,4)
def g_lower(k):
    v=F(k,n)
    return b*sqrt_lower(H2*(1-9*H2*v*v))-d*(1-9*H2*v)

total=F(0)
left=g_lower(0)
for k in range(1,n+1):
    right=g_lower(k)
    total+=positive_chord_mean(left,right)
    left=right
integral_lo=total/n
integral_hi=integral_lo+F(3,8*n*n)+F(1,10**15)
Llo=sqrt_lower(sum((x-y)**2 for x,y in zip(verts[2],verts[3])))
Hlo=sqrt_lower(H2)
vol_lo=area*Hlo*(1-3*H2) + Llo*Hlo*integral_lo/3
vol_hi=area*Hhi*(1-3*H2) + Lhi*Hhi*integral_hi/3
assert F("0.0529560390") < vol_lo <= vol_hi < F("0.052956040")
print(f"Constructed volume in ({float(vol_lo):.12f}, {float(vol_hi):.12f}) [display rounded].")
print("Exact certificate establishes 0.0529560390 < cover volume < 0.052956040.")
