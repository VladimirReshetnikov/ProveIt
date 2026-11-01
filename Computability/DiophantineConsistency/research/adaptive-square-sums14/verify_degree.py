#!/usr/bin/env python3
"""Check 14-variable graph residuals and exact degree; zero equivalence is open."""
import hashlib
import json
from pathlib import Path
D=Path(__file__).resolve().parent
raw=(D/'candidate.json').read_bytes()
if hashlib.sha256(raw).hexdigest()!='0c7451eaadba5569f2d901867c3e80deb0663e09bd51dd6972d1949eb1f669af':
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
      'sumSquares','squareConstraint','sumWithConstraint'}
for name,op,a,b in c['source']:
    if name in skip:continue
    x=P.lift(a) if isinstance(a,int) else g[a];y=P.lift(b) if isinstance(b,int) else g[b]
    g[name]=x+y if op=='+' else x-y if op=='-' else x*y
factors=[g[n] for n in ('A0','A1','auxResidual','g72','squareDifference')]
degrees=[max(sum(k[:14]) for k in f.d) for f in factors]
if degrees!=[15,13,8,10,12]:raise ValueError(('degrees',degrees))
key=tuple({'J':9,'X':2,'Y':2,'eta':2}.get(n,0) for n in names[:14])
coeff={k[14:]:v for k,v in factors[0].d.items() if k[:14]==key}
if coeff!={(9,0,0,0):-2}:raise ValueError(('first leading coefficient',coeff))
if (2**47)**2011-1<=0:raise ValueError('beta not positive')
expected_tail=[['squareDifference','-','squareWitness','g80'],
 ['squareConstraint','*','squareDifference','squareDifference'],
 ['sumWithConstraint','+','sumSquares','squareConstraint']]
if c['source'][-3:]!=expected_tail:raise ValueError('constraint wiring')
print('PASS residual degrees',degrees,'and exact output degree 30 after fixing ports and positive shift; zero equivalence remains open')
