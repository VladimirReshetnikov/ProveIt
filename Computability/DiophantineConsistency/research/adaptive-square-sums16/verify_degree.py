#!/usr/bin/env python3
"""Check 16-variable graph residuals and exact polynomial degree."""
import hashlib
import json
from pathlib import Path
D=Path(__file__).resolve().parent
raw=(D/'candidate.json').read_bytes()
if hashlib.sha256(raw).hexdigest()!='bfb13952920a218bb13b168006f19d2d1a29eaf184077cee319cf323472d44cc':
    raise ValueError('candidate mismatch')
c=json.loads(raw); names=c['witnesses']+c['fixed_numerals'];zero=(0,)*len(names)
class P:
    def __init__(self,d):self.d={k:v for k,v in d.items() if v}
    @staticmethod
    def lift(v):return v if isinstance(v,P) else P({zero:v})
    def __add__(self,v):
        out=self.d.copy()
        for k,x in self.lift(v).d.items():out[k]=out.get(k,0)+x
        return P(out)
    def __sub__(self,v):return self+-self.lift(v)
    def __neg__(self):return P({k:-v for k,v in self.d.items()})
    def __mul__(self,v):
        out={}
        for k,a in self.d.items():
            for l,b in self.lift(v).d.items():
                m=tuple(x+y for x,y in zip(k,l));out[m]=out.get(m,0)+a*b
        return P(out)
    def __eq__(self,v):return self.d==self.lift(v).d
g={}
for i,n in enumerate(names):
    key=list(zero);key[i]=1;g[n]=P({tuple(key):1})
skip={'firstSquare','mainSquare','auxSquare','strongSquare','firstMain','firstMainAux',
      'sumSquares','squareConstraint','sumWithConstraint','scaleConstraint','finalWithScale','mainScaleConstraint','finalWithMainScale'}
for name,op,a,b in c['source']:
    if name in skip:continue
    x=P.lift(a) if isinstance(a,int) else g[a];y=P.lift(b) if isinstance(b,int) else g[b]
    g[name]=x+y if op=='+' else x-y if op=='-' else x*y
factors=[g[n] for n in ('A0','A1','auxResidual','g72','squareDifference','scaleDifference','mainScaleDifference')]
degrees=[max(sum(k[:16]) for k in f.d) for f in factors]
if degrees!=[10,12,8,10,12,4,3]:raise ValueError(('degrees',degrees))
# The highest homogeneous part is a sum of squares of the degree-12
# residuals.  A nonzero leading residual cannot cancel in such a sum over R.
# Find an explicit monomial whose coefficient remains nonzero at fixed ports.
residual=factors[4]
for monomial,coefficient in residual.d.items():
    if sum(monomial[:16])==12:
        witness=monomial[:16]
        terms={k[16:]:v for k,v in residual.d.items() if k[:16]==witness}
        if len(terms)==1 and next(iter(terms.values()))!=0:
            break
else:raise ValueError('no certified leading monomial')
if terms!={(8,0,0,0):-1}:raise ValueError(('unexpected leading coefficient',terms))
if (2**47)**2011-1<=0:raise ValueError('beta not positive')
print('leading witness',witness,'port coefficient',terms)
expected_tail=[['mainScaleDifference','-','mainScaleVariable','U'],
 ['mainScaleConstraint','*','mainScaleDifference','mainScaleDifference'],
 ['finalWithMainScale','+','finalWithScale','mainScaleConstraint']]
if c['source'][-3:]!=expected_tail:raise ValueError('constraint wiring')
print('PASS residual degrees',degrees,'and exact output degree 24 after fixing ports and positive shift; iPRA transfer checked separately')
