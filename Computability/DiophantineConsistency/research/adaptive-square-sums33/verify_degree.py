#!/usr/bin/env python3
"""Check 33-variable graph residuals and exact polynomial degree."""
import hashlib
import json
from pathlib import Path
D=Path(__file__).resolve().parent
raw=(D/'candidate.json').read_bytes()
if hashlib.sha256(raw).hexdigest()!='a7934aac8f72dc632ebc86f15fa4300106b6af2e6ab5cd73e94f8bdd4c11e735':
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
      'sumSquares','squareConstraint','sumWithConstraint','scaleConstraint','finalWithScale','mainScaleConstraint','finalWithMainScale','rankConstraint','finalWithRank','cConstraint','aConstraint','ellConstraint','wConstraint','addC','addA','addEll','finalWithNamedValues','cubeConstraint','productConstraint','fSquareConstraint','cSquareConstraint','addCube','addProduct','addFSquare','addCSquare','zConstraint','dConstraint','vConstraint','deltaConstraint','addZConstraint','addDConstraint','addVConstraint','addDELTAConstraint'}
for name,op,a,b in c['source']:
    if name in skip:continue
    x=P.lift(a) if isinstance(a,int) else g[a];y=P.lift(b) if isinstance(b,int) else g[b]
    g[name]=x+y if op=='+' else x-y if op=='-' else x*y
factors=[g[n] for n in ('A0','A1','auxResidual','g72','squareDifference','scaleDifference','mainScaleDifference','rankDifference','cDifference','aDifference','ellDifference','wDifference','cubeDifference','productDifference','fSquareDifference','cSquareDifference','zDifference','dDifference','vDifference','deltaDifference')]
degrees=[max(sum(k[:33]) for k in f.d) for f in factors]
expected_degrees=[4,4,4,4,2,2,3,4,2,2,4,2,3,3,2,2,3,3,3,2]
if degrees!=expected_degrees:raise ValueError(('residual degrees',degrees))
print('residual degrees',degrees)
maximum=max(degrees)
# Any nonzero homogeneous residual of maximum degree gives a nonzero
# leading term of the sum of squares over the real polynomial ring.
for residual in factors:
    if max(sum(k[:33]) for k in residual.d)!=maximum: continue
    for monomial,coefficient in residual.d.items():
        if sum(monomial[:33])==maximum:
            witness=monomial[:33]
            terms={k[33:]:v for k,v in residual.d.items() if k[:33]==witness}
            if len(terms)==1 and next(iter(terms.values()))!=0:
                break
    else: continue
    break
else:raise ValueError('no certified leading monomial')
if terms not in ({(0,0,0,0):1},{(0,0,0,0):-1}):raise ValueError(('unexpected leading coefficient',terms))
print('leading witness',witness,'port coefficient',terms)
expected_tail=[['addZConstraint','+','addCSquare','zConstraint'],
 ['addDConstraint','+','addZConstraint','dConstraint'], ['addVConstraint','+','addDConstraint','vConstraint'],
 ['addDELTAConstraint','+','addVConstraint','deltaConstraint']]
if c['source'][-4:]!=expected_tail:raise ValueError('constraint wiring')
print('PASS exact output degree',2*maximum,'after fixing ports and positive shift; equivalence is outside this finite check')
