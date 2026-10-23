#!/usr/bin/env python3
"""Independent finite controls for the Sun B4 review; stdlib only.

No upstream generator or verifier is imported. These exact controls are
not substitutes for the universal proof or the imported bridge theorems.
"""
from pathlib import Path
from itertools import combinations_with_replacement,product
from math import factorial
import json,random

ROOT=Path(__file__).resolve().parent
SUN=ROOT.parent/'sun'

def require(p,message):
    if not p: raise ValueError(message)

weights=json.loads((SUN/'B4_OPTIMIZED.json').read_text())['witness_weights']
require(len(weights)==31 and min(weights)>0 and max(weights)==610895,'B4 dimensions')
positions=[0]+weights
sums=[sum(positions[i] for i in ix) for ix in combinations_with_replacement(range(32),4)]
require(len(sums)==52360 and len(set(sums))==52360,'B4 collision')

packing_checks=0
for n in range(1,8):
    N=1<<n
    for S in range(N):
        for T in range(N):
            R=(S+T+1)*N+T+1
            X=(N-1)*R
            identity=(S+T)*N*N+(N-1-S)*N+N-1-T
            require(X==identity,'packing identity')
            carries=S.bit_count()+T.bit_count()-(S+T).bit_count()
            require(X.bit_count()==2*n-carries,'packing valuation identity')
            require((X.bit_count()>=2*n)==((S&T)==0),'central-binomial criterion')
            packing_checks+=1

# Independent signed-coefficient example, with a known nonzero natural zero.
# P=(x-1)^2+(y-2)^2 has H0=5, P(0)=5 and the unique zero (1,2).
p={(0,0):5,(1,0):-2,(0,1):-4,(2,0):1,(0,2):1}
c={alpha:factorial(4-sum(alpha))*factorial(alpha[0])*factorial(alpha[1])*co
   for alpha,co in p.items()}
ww=[1,5];t=5;L=20;beta=1<<30
require(beta>48*(2+2)**4*5,'toy scale')
rng=random.Random(20261023)
source_checks=0
for b in [4,16,64]:
    B=beta*b**4;cap=b*B**t;N0=B**(t+1);N1=4*B**(8*t+1);N=N0*N1
    ell=sum(B**w for w in ww)
    D=sum(co*B**(L-sum(a*w for a,w in zip(alpha,ww))) for alpha,co in c.items())
    mask=N0-1-(b-1)*ell
    Tc=mask+(B-2)*B**L*N0
    offset=sum(B**j for j in range(1,8*t+2))
    require(D>0 and 0<=mask<N0 and 0<=Tc<N,'toy static bounds')
    points=list(product(range(min(b,8)),repeat=2))
    cases=[(sum(ni*B**wi for ni,wi in zip(point,ww)),point) for point in points]
    cases += [(rng.randrange(0,2*cap),None) for _ in range(200)]
    cases += [(g,None) for g in [0,1,b-1,b,cap,2*cap-1]]
    for g,point in cases:
        Jc=2*(1+g)**4*D+offset
        Sc=g+Jc*N0
        Rc=(Sc+Tc+1)*N+Tc+1
        X=(N-1)*Rc;Y=N*N
        require(0<Jc<2*B**(8*t+1)<N1,'arbitrary-g carry bound')
        require(0<=Sc<N and 0<=Tc<N,'arbitrary-g packing bounds')
        require(X%3==0 and X>3*b and Y>max(b,256),'Sun source numerical hypotheses')
        if point is not None:
            no_carry=(Sc&Tc)==0
            pvalue=(point[0]-1)**2+(point[1]-2)**2
            require(no_carry==(pvalue==0),'toy sparse coefficient extraction')
            require((X.bit_count()>=2*(N.bit_length()-1))==(pvalue==0),'toy divisibility decode')
        source_checks+=1

out=dict(status='PASS',B4_four_multisets=len(sums),packing_pairs=packing_checks,
         signed_coefficient_toy_assignments=source_checks,
         generator_imported=False,verifier_imported=False,
         scope='Exact finite controls for a separate mathematical review, not proof of the imported Sun bridge or K215 endpoint.')
(ROOT/'SUN_B4_INDEPENDENT_CHECKS.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
