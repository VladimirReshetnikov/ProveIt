from pathlib import Path
from fractions import Fraction
from math import factorial, comb, sqrt, pi
import json

def success(m,k):
    q=[(-1)**j*factorial(m-1)//factorial(m-1-j) for j in range(m)]
    p=[1]
    for _ in range(k):
        r=[0]*(len(p)+m-1)
        for i,a in enumerate(p):
            for j,b in enumerate(q):r[i+j]+=a*b
        p=r
    den=factorial(k+len(p)-1)
    total=sum(a*(den//factorial(k+j)) for j,a in enumerate(p))
    return Fraction(m**k*total,den)

rows=[]
for m in [1,2,3,4,5,7,10,15,20,30,40]:
 p=success(m,m); W=factorial(m*m)//factorial(m)**m
 a=p*W; assert a.denominator==1
 c=sqrt(m)*(float(p)-.5)
 r={'m':m,'P':str(float(p)),'a':str(a.numerator),'sqrt_m_residual':c,'target':4/(3*sqrt(2*pi)),'first_error':float(p)-.5-4/(3*sqrt(2*pi*m))}
 print(r,flush=True);rows.append(r)
open((Path(__file__).resolve().parent.parent/'checks'/'renewal-exact-checks.json'),'w').write(json.dumps(rows,indent=2))
