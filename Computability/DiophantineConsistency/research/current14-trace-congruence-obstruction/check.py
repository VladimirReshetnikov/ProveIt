#!/usr/bin/env python3
"""Finite control for the direct ordinate-congruence trace proposal."""
import json,math
q,X,Y,R=2,2,16,5
a=Y*(X+1);H=4*a+3;A=a+2
x,y=1,0
for _ in range(R):x,y=A*x+(A*A-1)*y,x+A*y
c=y;power=1<<R
res=3*X*c-2*(X*X-1)
assert X%q==0 and Y%(q**3)==0 and R+1<X*Y
assert H==195 and c==99970001 and res>0 and res%H==0
assert res//H==3076000 and X!=power
assert (X-power)*(power*X+1)%H==0 and math.gcd(power*X+1,H)==65
print(json.dumps({'q':q,'X':X,'Y':Y,'R':R,'H':H,'c':c,'alternative_gamma':res//H,'gcd':math.gcd(power*X+1,H),'scope':'local ordinary arithmetic counterexample; not a full consistency-equation zero'},sort_keys=True,indent=2))
