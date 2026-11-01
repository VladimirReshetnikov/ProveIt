#!/usr/bin/env python3
"""Replace the scaled main root by its positive quotient."""
import hashlib
import json
from pathlib import Path
D=Path(__file__).resolve().parent
raw=(D.parent/'adaptive-square-sums41-quartic/candidate.json').read_bytes()
if hashlib.sha256(raw).hexdigest()!='62e7851fa8cfee544f92b83ff4f422e200f10c4a45f0e236d83e1ac3f07dd239':
    raise ValueError('parent pin')
p=json.loads(raw);w=p['witnesses']
if w[24]!='dValueVariable' or w[30]!='varphiSquareVariable':
    raise ValueError('unexpected main-root coordinates')
w=['mainQuotient' if name=='dValueVariable' else name for name in w if name!='varphiSquareVariable']
expected={'g61':['g61','*','dValueVariable','dValueVariable'],
 'g62':['g62','*','mainScaleVariable','mainScaleVariable'],
 'g64':['g64','+',1,'deltaProductVariable'], 'g65':['g65','*','varphiSquareVariable','g64'],
 'A1':['A1','-','g61','g65'], 'dDifference':['dDifference','-','dValueVariable','DstarComputed'],
 'varphiSquareDifference':['varphiSquareDifference','-','varphiSquareVariable','g62'],
 'varphiSquareConstraint':['varphiSquareConstraint','*','varphiSquareDifference','varphiSquareDifference'],
 'add_varphiSquare':['add_varphiSquare','+','add_ellProduct','varphiSquareConstraint'],
 'add_scaledIndex':['add_scaledIndex','+','add_varphiSquare','scaledIndexConstraint']}
table={r[0]:r for r in p['source']}
if any(table.get(k)!=v for k,v in expected.items()):raise ValueError('parent bindings changed')
rows=[]
for name,op,left,right in p['source']:
    if name in {'g62','g65','varphiSquareDifference','varphiSquareConstraint','add_varphiSquare'}:continue
    if name=='dDifference':
        rows.append(['dScaled','*','mainScaleVariable','mainQuotient']);left='dScaled'
    if name=='A1':right='g64'
    if name=='add_scaledIndex':left='add_ellProduct'
    left='mainQuotient' if left=='dValueVariable' else left
    right='mainQuotient' if right=='dValueVariable' else right
    rows.append([name,op,left,right])
table={r[0]:r for r in rows};known=set(w+p['fixed_numerals'])
for name,op,left,right in rows:
    if name in known or any(isinstance(x,str) and x not in known for x in (left,right)):raise ValueError(('topology',name))
    known.add(name)
live={p['output']};todo=list(live)
while todo:
    name=todo.pop()
    if name in table:
        for x in table[name][2:]:
            if isinstance(x,str) and x not in live:live.add(x);todo.append(x)
if not set(table)<=live or not set(w+p['fixed_numerals'])<=live:raise ValueError('dead node or input')
if len(w)!=40 or len(rows)!=166:raise ValueError(('size',len(w),len(rows)))
out={'scope':'Candidate only; main quotient transport and native iPRA endpoint remain open.',
     'witnesses':w,'fixed_numerals':p['fixed_numerals'],'source':rows,'output':p['output'],'operations':len(rows)}
(D/'candidate.json').write_text(json.dumps(out,indent=2)+'\n')
print('PASS: 40 variables, 166 live rows; main quotient transport remains open')
