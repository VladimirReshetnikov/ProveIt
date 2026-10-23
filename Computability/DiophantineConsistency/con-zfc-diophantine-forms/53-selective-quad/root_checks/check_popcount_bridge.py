#!/usr/bin/env python3
"""Independent exhaustive finite audit of the two-block carry bridge.
Finite checks corroborate the algebraic proof, not the Con(ZFC) equivalence.
"""
import json
from pathlib import Path

def require(p,msg):
    if not p: raise AssertionError(msg)

cases=0
for u in range(1,9):
    N=1<<u
    for S in range(N):
        for T in range(N-S):
            X=N*N+(S+T)*N+(N-1-S)
            v=X.bit_count()
            carry=S.bit_count()+T.bit_count()-(S+T).bit_count()
            target=u+T.bit_count()+1
            require(v==target-carry,(u,S,T,'identity'))
            require((v>=target)==((S&T)==0),(u,S,T,'zero carry'))
            require(carry>=0,(u,S,T,'nonnegative'))
            if u%2==0 and T%3==2: require(X%3==0,(u,S,T,'mod3'))
            cases+=1
# Addition overflow is not covered by the block proof.
# This counterexample prevents silently dropping the S+T<N hypothesis.
u=2;N=1<<u;S=T=3
X=N*N+(S+T)*N+(N-1-S)
require(X.bit_count()!=u+T.bit_count()+1-(S.bit_count()+T.bit_count()-(S+T).bit_count()),'overflow negative control')
out={'status':'PASS','exhaustive_cases':cases,'u_range':[1,8], 'overflow_control':'rejected','claim_scope':'finite identity checks only'}
Path(__file__).with_suffix('.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out))
