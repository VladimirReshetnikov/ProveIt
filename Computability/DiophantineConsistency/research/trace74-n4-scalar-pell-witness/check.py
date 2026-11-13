#!/usr/bin/env python3
"""Exact scalar Pell witness; no 74 graph evaluation."""
import hashlib
import json
import sys
from math import comb

if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:
    raise SystemExit('use python3 -I -S -B without optimization')

def ycoord(n, b):
    x, y = 1, 0
    for _ in range(n):
        x, y = (b+2)*x+(b+1)*(b+3)*y, x+(b+2)*y
    return y

q = 32
beta, J = 31, 1
Y = q**3
X = 8*Y**3
P = X*Y**2
A = Y*(X+1)
n, r = 4, 5
k = 2*ycoord(n, 2*(P-1)+1)
c = ycoord(r, A-1)
eta = c-k*Y
zeta = k-eta

assert q == beta*J+1 and q >= 32
assert X > 0 and Y > 0 and X % q == 0 and Y % (q**3) == 0
assert 0 < n < r < 2*n and r % 2 == 1
assert k == 128*P**3+192*P**2+80*P+8
assert c == 16*(A+1)**4-12*(A+1)**2+1
assert 0 < eta < k and zeta > 0
assert k == eta+zeta and c == k*Y+eta

def digest(n):
    return hashlib.sha256(n.to_bytes((n.bit_length()+7)//8 or 1, 'big')).hexdigest()

def add(a, b):
    r = dict(a)
    for k0, v in b.items(): r[k0] = r.get(k0, 0)+v
    return {k0:v for k0,v in r.items() if v}
def scale(n0, a): return {i:n0*v for i,v in a.items() if n0*v}
def mul(a, b):
    r = {}
    for i,u in a.items():
        for j,v in b.items(): r[i+j] = r.get(i+j, 0)+u*v
    return {i:v for i,v in r.items() if v}
def power(a, n0):
    r = {0:1}
    for _ in range(n0): r = mul(r, a)
    return r
def shift_two(a):
    return {j:sum(v*comb(i,j)*2**(i-j) for i,v in a.items() if i>=j)
            for j in range(max(a)+1)}

# Verify y4=8t³−4t and y5=16t⁴−12t²+1 for t=b+2 by recurrence.
t0 = {1:1}
xx0, yy0 = {0:1}, {}
ys = {}
for i in range(1, 6):
    xx0, yy0 = add(mul(t0,xx0),mul(add(power(t0,2),{0:-1}),yy0)), add(xx0,mul(t0,yy0))
    ys[i] = yy0
assert ys[4] == add(scale(8,power(t0,3)),scale(-4,t0))
assert ys[5] == add(add(scale(16,power(t0,4)),scale(-12,power(t0,2))),{0:1})

# Universal scalar family: Y is formal, X=8Y³.  Both eta(Y) and
# zeta(Y) have strictly positive coefficients after Y=2+u, u>=0.
yy, xx, one = {1:1}, {3:8}, {0:1}
pp = mul(xx, power(yy, 2))
tt = add(mul(yy, add(xx, one)), one)
kk = add(add(scale(128,power(pp,3)),scale(192,power(pp,2))),add(scale(80,pp),{0:8}))
cc = add(add(scale(16,power(tt,4)),scale(-12,power(tt,2))),one)
ee = add(cc,scale(-1,mul(kk,yy)))
zz = add(kk,scale(-1,ee))
ee2, zz2 = shift_two(ee), shift_two(zz)
assert all(v>0 for v in ee2.values()) and all(v>0 for v in zz2.values())

print(json.dumps({'status':'PASS','q':q,'beta':beta,'J':J,'X':X,'Y':Y,'n':n,'r':r,
                  'k_bits':k.bit_length(),'c_bits':c.bit_length(),
                  'eta_bits':eta.bit_length(),'zeta_bits':zeta.bit_length(),
                  'k_sha256_be':digest(k),'c_sha256_be':digest(c),
                  'eta_sha256_be':digest(eta),'zeta_sha256_be':digest(zeta),
                  'universal_Y_ge_2_eta_terms':len(ee2),'universal_Y_ge_2_zeta_terms':len(zz2),
                  'universal_eta_shift_constant':ee2[0],'universal_zeta_shift_constant':zz2[0],
                  'scope':'ordinary integer scalar Pell witness only; no 74 graph zero, rank, ports or iPRA claim'},
                 sort_keys=True))
