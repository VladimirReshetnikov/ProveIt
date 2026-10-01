#!/usr/bin/env python3
import sympy as s
from math import comb
from pathlib import Path
import json
n=m=9;w=100
def bn(n,k):return comb(n,k) if 0<=k<=n else 0
p=[sum(comb(2,i)*comb(3,j)*bn(n,k-i)*bn(m,k-j)*w**(i+j) for i in range(3) for j in range(4) if i+j>=k and i<=k and j<=k) for k in range(6)]
scaled=[s.Rational(c,100**k) for k,c in enumerate(p)]
assert scaled==[1,645,38730,124500,37800,3024]
t=s.symbols('t');P=s.Poly(sum(c*t**k for k,c in enumerate(scaled)),t)
disc=s.discriminant(P.as_expr(),t)
assert disc==-4431992565218959594687680000000
margins=[k*(5-k)*scaled[k]**2-(k+1)*(6-k)*scaled[k-1]*scaled[k+1] for k in range(1,5)]
assert margins==[1276800,8036447400,75433572000,1950480000]
assert P.count_roots(-s.oo,s.oo)==3
out={'scaled_coefficients':list(map(int,scaled)),'discriminant':str(disc),'real_roots':3,'rank_five_margins':list(map(int,margins)),'all_checks_passed':True}
Path(__file__).with_name('separation_verification.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
