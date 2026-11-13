#!/usr/bin/env python3
"""Exact Pell-coordinate witness showing why eta < k matters to the bound."""
def ordinate(n,b):
    x,y=1,0
    for _ in range(n):
        x,y=(b+2)*x+(b+1)*(b+3)*y, x+(b+2)*y
    return y
X,Y,r=16,1,2
B=2*(X*Y*Y-1)+1
k=2*ordinate(r+1,B)
c=ordinate(2*r+1,Y*(X+1))
eta=c-k*Y
assert X>=16 and Y>=1 and r>=2
assert (B,k,c,eta)==(31,8710,2080805,2072095)
assert c==k*Y+eta and eta>=k>0
assert not 2**(2*r+1)<Y
print(f'X={X}, Y={Y}, r={r}, B={B}, k={k}, c={c}, eta={eta}, 2^(2r+1)={2**(2*r+1)}')
