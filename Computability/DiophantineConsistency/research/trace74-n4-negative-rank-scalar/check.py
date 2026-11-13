#!/usr/bin/env python3
"""Exact scalar obstruction with an explicit failing graph-projection check."""
import hashlib
import json
from math import gcd
import sys

if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:
    raise SystemExit('use python3 -I -S -B without optimization')

def ycoord(n, b):
    x, y = 1, 0
    for _ in range(n):
        x, y = (b+2)*x+(b+1)*(b+3)*y, x+(b+2)*y
    return y

q, beta, J, MC, MF = 32, 31, 1, 1, 32
Y = q**3
X = 8*Y**3
P = X*Y**2
A = Y*(X+1)
n, r = 4, 5
k = 2*ycoord(n, 2*(P-1)+1)
c = ycoord(r, A-1)
eta = c-k*Y
zeta = k-eta
D = q**2-1
M = (MC+q*MF)*J
t = 975595108
rank = -(5+t*c)
F = 1
assert (rank-M) % D == 0
C = q**2-q*F-(rank-M)//D

assert q == beta*J+1 and 0 < MC < beta < MF < 2*beta
assert X % q == 0 and Y % (q**3) == 0 and X >= 32 and Y >= 1
assert 0 < n < r < 2*n and r % 2 == 1
assert k == 128*P**3+192*P**2+80*P+8
assert c == 16*(A+1)**4-12*(A+1)**2+1
assert eta > 0 and zeta > 0 and k == eta+zeta and c == k*Y+eta
assert F > 0 and C > 0 and rank < 0
assert rank == (q*(q-F)-C)*D+M
assert (rank+1-k) % (q**4) == 0
assert abs(rank) % c == r % c and c > 2*q**4
assert rank+q**3+q+1 <= q**4

# The checked graph projection is an additional necessary condition.
# It FAILS here, so this tuple is certainly not a graph zero satisfying it.
h = beta*J
H = 4*A-1
product = (h*X)*(X-2**r)*(2**r*X+1)
assert product % H != 0
assert gcd(H, product) == 3

def digest(z):
    z = abs(z)
    return hashlib.sha256(z.to_bytes((z.bit_length()+7)//8 or 1, 'big')).hexdigest()

print(json.dumps({'status':'PASS','q':q,'beta':beta,'J':J,'MC':MC,'MF':MF,
                  'X':X,'Y':Y,'n':n,'r':r,'F':F,'t':t,'H':H,
                  'C_bits':C.bit_length(),'negative_rank_bits':(-rank).bit_length(),
                  'C_sha256_be':digest(C),'abs_rank_sha256_be':digest(rank),
                  'projection_divides':False,'projection_gcd':gcd(H,product),
                  'scope':'ordinary integer scalar diagnostic; explicitly fails a necessary graph projection; not a 74 zero or fixed-BFS claim'},sort_keys=True))
