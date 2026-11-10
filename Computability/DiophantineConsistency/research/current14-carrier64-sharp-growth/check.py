#!/usr/bin/env python3
"""Exact polynomial and finite recurrence controls for sharp Pell bounds."""
from collections import Counter
import hashlib
import json
from pathlib import Path
HERE=Path(__file__).resolve().parent;D=HERE.parents[1]
pins={
 'research/current14-carrier64-two-sided-window-partial/result.json':'aa702fdb63e365347cc9bd9317dc46d48608746ad5b73665e43616ce4deb8cf0',
 'research/current14-carrier64-growth-window/result.json':'a5a505411bfdb54e1714827060cf39038d7adff6ae3244643406b932469b342b'}
for name,digest in pins.items():
    if hashlib.sha256((D/name).read_bytes()).hexdigest()!=digest: raise RuntimeError('pin mismatch')
partial=json.loads((D/'research/current14-carrier64-two-sided-window-partial/result.json').read_bytes())
if not (partial['Y']=='X^N' and partial['R_odd']): raise RuntimeError('partial shape mismatch')

# Verify exact numerator identity in Z[X,Y].
one={(0,0):1}; X={(1,0):1}; Y={(0,1):1}
def scale(n,p): return {k:n*v for k,v in p.items() if n*v}
def add(a,b):
    out=Counter(a);out.update(b)
    return {k:v for k,v in out.items() if v}
def sub(a,b):return add(a,scale(-1,b))
def mul(a,b):
    out=Counter()
    for x,cx in a.items():
        for y,cy in b.items():out[tuple(s+t for s,t in zip(x,y))]+=cx*cy
    return {k:v for k,v in out.items() if v}
xp=add(X,one); Y2=mul(Y,Y)
base=add(scale(2,mul(Y,xp)),scale(3,one))
den=add(scale(4,mul(X,Y2)),scale(2,one))
lhs=sub(mul(base,base),mul(xp,den))
rhs=add(mul(xp,sub(add(scale(4,Y2),scale(12,Y)),scale(2,one))),scale(9,one))
if lhs!=rhs:raise RuntimeError('Pell-base inequality identity failed')

recurrence_cases=0
for p in range(2,31):
    prev,cur=0,1
    for n in range(1,41):
        if not ((2*p-1)**(n-1)<=cur<=(2*p)**(n-1)):
            raise RuntimeError('sharpened recurrence controls failed')
        prev,cur=cur,2*p*cur-prev
        recurrence_cases+=1
upper_cases=0
for R in range(27,100,2):
    Xval=1<<R;N=(R-1)//2
    if not (Xval>8*N and (Xval+2)**(2*N)<2*Xval**(2*N)):
        raise RuntimeError('exponential control failed')
    upper_cases+=1
print(json.dumps({'pins':pins,'checker_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
 'base_difference':'exact sparse polynomial, positive for X,Y>=1',
 'recurrence_control_cases':recurrence_cases,'upper_control_cases':upper_cases,
 'partial_Y_equals_X_to_N':True,
 'scope':'external theorem consequence with finite controls; no Lean run or general reverse equivalence'},
 sort_keys=True,indent=2))
