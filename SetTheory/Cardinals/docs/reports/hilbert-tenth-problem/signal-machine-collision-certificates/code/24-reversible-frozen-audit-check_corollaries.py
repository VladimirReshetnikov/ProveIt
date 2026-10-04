#!/usr/bin/env python3
"""New supplementary checks for the compact rejection witness and arithmetic."""
import json
from pathlib import Path
from fractions import Fraction
from independent_checker import A, raw, swap, statuses, step, require
root=Path(__file__).resolve().parent
x=frozenset((-8,-5,0,1));y=swap(x,('AR',0))
require(raw(x,A)=={('AR',0):0},'raw x')
require(set(raw(y,A))=={('AR',0),('AC',-7)},'birth missed')
require(statuses(x,A)=={('AR',0):(True,False)},'prospective must reject')
require(step(x,A)[0]==x and step(y,A)[0]==y,'actual rejection')
z=x|frozenset((70,71));out,keys,status=step(z,A)
require(out==x|frozenset((70,72)),'remote selected/rejected interaction')
require(status=={('AR',0):(True,False),('AR',70):(True,True)},'remote statuses')
integers=0;rationals=0
for a in (0,1,2,13,10**10,10**100):
    for k in (0,1,2,3,30,10**20,10**100):
        t=k*k+(2*a+3)*k
        require((k*k+(2*a+3)*k-t)**2==0,'quartic root')
        require((k+1)**2+(2*a+3)*(k+1)-t==2*k+2*a+4,'monotone gap')
        other=-k-(2*a+3)
        require(other*other+(2*a+3)*other-t==0 and other<0,'signed second root')
        integers+=1
# Finite check supplements the rational-root theorem, not proves it.
for a in range(8):
    for t in range(200):
        for den in range(1,13):
            for num in range(1,80):
                k=Fraction(num,den)
                if k*k+(2*a+3)*k==t:require(k.denominator==1,'rational false root')
                rationals+=1
result={'all_checks_passed':True,'compact_rejection':{'input':sorted(x),'hypothetical':sorted(y),
    'new_key':['AC',-7]},'simultaneous_selected_and_rejected':{'input':sorted(z),'output':sorted(out)},
    'large_integer_quartic_checks':integers,'rational_trials':rationals,
    'proof_scope':'Monic rational-root theorem and strict monotonicity, not trial enumeration, establish the general fiber claims.'}
(root/'corollary-results.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
