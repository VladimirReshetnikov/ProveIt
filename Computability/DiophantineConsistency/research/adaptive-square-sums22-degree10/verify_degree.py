#!/usr/bin/env python3
"""Check 22-variable graph residuals and exact polynomial degree."""
import hashlib
import json
from pathlib import Path
if not __debug__:
    raise RuntimeError('optimized Python is not supported')
D=Path(__file__).resolve().parent
raw=(D/'candidate.json').read_bytes()
if hashlib.sha256(raw).hexdigest()!='1266b143c5512351739ea2c71fc8e0b8b0e5cecc599392f128c0803ff78ce106':
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
factors_names=['A0','A1','auxResidual','g72','scaleDifference','mainScaleDifference','rankDifference','ellDifference','cSquareDifference','zDifference','dDifference','vDifference','deltaDifference']
rows={row[0]:row for row in c['source']}; live=set(factors_names); todo=list(live)
square_names = ['firstSquare', 'mainSquare', 'auxSquare', 'strongSquare',
                'scaleConstraint', 'mainScaleConstraint', 'rankConstraint',
                'ellConstraint', 'cSquareConstraint', 'zConstraint',
                'dConstraint', 'vConstraint', 'deltaConstraint']
for factor, square in zip(factors_names, square_names):
    if rows.get(square) != [square, '*', factor, factor]:
        raise ValueError(('square wiring', factor))
sums = [
    ('firstMain', 'firstSquare', 'mainSquare'),
    ('firstMainAux', 'firstMain', 'auxSquare'),
    ('sumSquares', 'firstMainAux', 'strongSquare'),
    ('finalWithScale', 'sumSquares', 'scaleConstraint'),
    ('finalWithMainScale', 'finalWithScale', 'mainScaleConstraint'),
    ('finalWithRank', 'finalWithMainScale', 'rankConstraint'),
    ('addEll', 'finalWithRank', 'ellConstraint'),
    ('addCSquare', 'addEll', 'cSquareConstraint'),
    ('addZConstraint', 'addCSquare', 'zConstraint'),
    ('addDConstraint', 'addZConstraint', 'dConstraint'),
    ('addVConstraint', 'addDConstraint', 'vConstraint'),
    ('addDELTAConstraint', 'addVConstraint', 'deltaConstraint'),
]
for result, left, right in sums:
    if rows.get(result) != [result, '+', left, right]:
        raise ValueError(('sum wiring', result))
while todo:
    name=todo.pop()
    if name in rows:
        for dep in rows[name][2:]:
            if isinstance(dep,str) and dep not in live: live.add(dep);todo.append(dep)
for name,op,a,b in c['source']:
    if name not in live:continue
    x=P.lift(a) if isinstance(a,int) else g[a];y=P.lift(b) if isinstance(b,int) else g[b]
    g[name]=x+y if op=='+' else x-y if op=='-' else x*y
factors=[g[n] for n in factors_names]
degrees=[max(sum(k[:22]) for k in f.d) for f in factors]
if len(degrees)!=13 or max(degrees)!=5:raise ValueError(('residual degrees',degrees))
print('residual degrees',degrees)
maximum=max(degrees)
# Any nonzero homogeneous residual of maximum degree gives a nonzero
# leading term of the sum of squares over the real polynomial ring.
for residual in factors:
    if max(sum(k[:22]) for k in residual.d)!=maximum: continue
    for monomial,coefficient in residual.d.items():
        if sum(monomial[:22])==maximum:
            witness=monomial[:22]
            terms={k[22:]:v for k,v in residual.d.items() if k[:22]==witness}
            if terms in ({(0,0,0,0):1},{(0,0,0,0):-1}):
                break
    else: continue
    break
else:raise ValueError('no certified leading monomial')
if terms not in ({(0,0,0,0):1},{(0,0,0,0):-1}):raise ValueError(('unexpected leading coefficient',terms))
print('leading witness',witness,'port coefficient',terms)
if c['output'] != 'addDELTAConstraint':raise ValueError('unexpected output')
if maximum != 5:raise ValueError(('unexpected degree', maximum))
print('PASS candidate degree', 2 * maximum, 'after positive shift; zero-set equivalence is outside this finite check')
