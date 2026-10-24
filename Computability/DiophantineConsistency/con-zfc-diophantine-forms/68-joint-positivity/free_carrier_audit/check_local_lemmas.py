#!/usr/bin/env python3
"""Independent finite regressions. These do not replace the accompanying proof."""
import json
from pathlib import Path
from math import gcd
counts={}
count=0
for A in range(-80,81):
    if not A: continue
    u0,u1=0,1
    for n in range(1,301):
        value=u1
        if n%2:
            expected=(-1)**((n-1)//2)
        else:
            r=n//2
            expected=(-1)**(r-1)*r*A
        assert (value-expected)%(A*A)==0,(A,n)
        count+=1
        u0,u1=u1,A*u1-u0
counts['paired_recurrence_mod_A_squared']=count
count=0
for t in range(-15,16):
    b=6*t+4
    for j in range(-12,13):
        for c in range(-12,13):
            A=2*b*j
            C=b*c-1
            D=(A*A-4)*C*C+4
            assert D%(4*b)==0
            assert C%2==1
            for Q in [-7,-5,-3,-1,1,3,5,7]:
                # Q only assumed odd for unconditional square-class separation.
                for delta in [-1,0,1]:
                    z=2
                    a=b*Q+(3*delta-1)*(b*Q*z)**2
                    d=D*3*5
                    assert (a//b)%2==1 and (d//b)%2==0 and a!=d
            count+=1
counts['minimal_congruence_C_b_c_minus_one']=count
count=0
for L in range(-51,52):
    if not L:continue
    S=4*L-1;M=S*L
    assert gcd(S,L)==1
    for T in range(-8,9):
        for J in range(-8,9):
            R=T+S*(T-J)
            assert (R%M==0)==(T%S==0 and J%L==0)
            count+=1
counts['signed_CRT_equivalence']=count
count=0
for aa in range(-20,21):
 for cc in range(-20,21):
  A=6*aa;C=6*cc-1;D=(A*A-4)*C*C+4
  assert D%3==0 and C%2==1
  for rr in range(-8,9):
   r=3*rr+1
   for Delta in range(-5,6):
    delta=9*Delta-3
    assert delta%3==0 and delta%9==6
    for z in [-2,-1,0,1,2]:
     a=r+delta*(r*z)**2
     assert a%3==1 and a!=D*7*11
    count+=1
counts['fixed_mod_three_separation']=count
out={'status':'PASS','scope':'Finite regressions only; unbounded claims proved in companion mathematical audit.','checks':counts}
Path(__file__).with_name('LOCAL_CHECKS.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
