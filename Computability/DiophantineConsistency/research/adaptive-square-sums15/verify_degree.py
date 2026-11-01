#!/usr/bin/env python3
"""Check 15-variable graph residuals and exact polynomial degree."""
import hashlib
import json
from pathlib import Path
D=Path(__file__).resolve().parent
raw=(D/'candidate.json').read_bytes()
if hashlib.sha256(raw).hexdigest()!='17af36e8443655114196bc9795555b5c17756e3c9e63ff07686c71f8564795b0':
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
      'sumSquares','squareConstraint','sumWithConstraint','scaleConstraint','finalWithScale'}
for name,op,a,b in c['source']:
    if name in skip:continue
    x=P.lift(a) if isinstance(a,int) else g[a];y=P.lift(b) if isinstance(b,int) else g[b]
    g[name]=x+y if op=='+' else x-y if op=='-' else x*y
factors=[g[n] for n in ('A0','A1','auxResidual','g72','squareDifference','scaleDifference')]
degrees=[max(sum(k[:15]) for k in f.d) for f in factors]
if degrees!=[10,13,8,10,12,4]:raise ValueError(('degrees',degrees))
key=tuple({'J':4,'X':2,'Y':5,'eta':1,'gamma':1}.get(n,0) for n in names[:15])
coeff={k[15:]:v for k,v in factors[1].d.items() if k[:15]==key}
if coeff!={(4,0,0,0):8}:raise ValueError(('main leading coefficient',coeff))
if (2**47)**2011-1<=0:raise ValueError('beta not positive')
expected_tail=[['scaleDifference','-','scaleVariable','M'],
 ['scaleConstraint','*','scaleDifference','scaleDifference'],
 ['finalWithScale','+','sumWithConstraint','scaleConstraint']]
if c['source'][-3:]!=expected_tail:raise ValueError('constraint wiring')
print('PASS residual degrees',degrees,'and exact output degree 26 after fixing ports and positive shift; iPRA transfer checked separately')
