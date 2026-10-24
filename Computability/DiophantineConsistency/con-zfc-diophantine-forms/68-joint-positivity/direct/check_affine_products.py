#!/usr/bin/env python3
from math import factorial,gcd,prod
from itertools import combinations_with_replacement,combinations,product
import json
checks=0
for m in range(1,101):
    M=factorial(m)
    for i in range(1,m+1):
        for j in range(i+1,m+1):
            assert gcd(1+i*M,1+j*M)==1
            checks+=1
F=range(3);M=2
prem=[()]+[(i,) for i in F]+list(combinations_with_replacement(F,2))
rules=[(p,c) for p in prem for c in F]
certs=cases=0
for k in range(4):
  for rs in combinations(rules,k):
    for ns in product(range(3),repeat=k):
      v=[0]*3;left=right=1
      for (p,c),n in zip(rs,ns):
        v[c]+=n
        left*=pow(1+c*M,n)
        for a in p:
          v[a]-=n;right*=pow(1+a*M,n)
      for t in (1,2):
        equality=left==(1+t*M)*right
        balance=all(v[j]==int(j==t) for j in (1,2))
        assert equality==balance
        certs+=equality;cases+=1
assert (1+1*1)**2==1+3*1 # bad M=1 collision control
print(json.dumps({'status':'pass','pairwise_gcd_checks':checks,'product_balance_comparisons':cases,'certificates':certs,'negative_control':'M=1 collision at labels1,3','scope':'finite arithmetic regressions, not global compilation'},indent=2))
