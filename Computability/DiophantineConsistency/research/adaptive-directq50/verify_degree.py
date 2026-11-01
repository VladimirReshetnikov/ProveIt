#!/usr/bin/env python3
"""Check 50-variable graph residuals and exact polynomial degree."""
import hashlib
import json
from pathlib import Path
D=Path(__file__).resolve().parent
raw=(D/'candidate.json').read_bytes()
if hashlib.sha256(raw).hexdigest()!='4022b140734fb723f39d13d3867bd67f1432c9651f392110b14f643892905bf2':
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
factors_names=['A0','A1','auxResidual','g72','squareDifference','scaleDifference','mainScaleDifference','rankDifference','cDifference','aDifference','ellDifference','wDifference','cubeDifference','productDifference','fSquareDifference','cSquareDifference','zDifference','dDifference','vDifference','deltaDifference','qSquareDifference','product2Difference','psiSquareDifference','ellProductDifference','varphiSquareDifference','scaledIndexDifference','ySquareDifference','qSignedDifference','deltaProductDifference','rankSeedDifference','ySumDifference','rootSkewDifference','offsetDifference','gammaProductDifference','timeProductDifference']
rows={row[0]:row for row in c['source']}; live=set(factors_names); todo=list(live)
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
degrees=[max(sum(k[:50]) for k in f.d) for f in factors]
expected_degrees=[2,2,2,2,2,2,2,2,1,1,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2]
if degrees!=expected_degrees:raise ValueError(('residual degrees',degrees))
print('residual degrees',degrees)
maximum=max(degrees)
# Any nonzero homogeneous residual of maximum degree gives a nonzero
# leading term of the sum of squares over the real polynomial ring.
for residual in factors:
    if max(sum(k[:50]) for k in residual.d)!=maximum: continue
    for monomial,coefficient in residual.d.items():
        if sum(monomial[:50])==maximum:
            witness=monomial[:50]
            terms={k[50:]:v for k,v in residual.d.items() if k[:50]==witness}
            if len(terms)==1 and next(iter(terms.values()))!=0:
                break
    else: continue
    break
else:raise ValueError('no certified leading monomial')
if terms not in ({(0,0,0,0):1},{(0,0,0,0):-1}):raise ValueError(('unexpected leading coefficient',terms))
print('leading witness',witness,'port coefficient',terms)
labels=['deltaProduct','rankSeed','ySum','rootSkew','offset','gammaProduct','timeProduct']
for label in labels:
    if rows[label+'Constraint']!=[label+'Constraint','*',label+'Difference',label+'Difference']:raise ValueError(('constraint square',label))
prev='add_qSigned'
for label in labels:
    name='add_'+label
    if rows[name]!=[name,'+',prev,label+'Constraint']:raise ValueError(('sum wiring',label))
    prev=name
if c['output']!=prev:raise ValueError('wrong output')
if maximum!=2:raise ValueError(('unexpected degree',maximum))
print('PASS candidate degree',2*maximum,'after positive shift; zero-set equivalence is outside this finite check')
