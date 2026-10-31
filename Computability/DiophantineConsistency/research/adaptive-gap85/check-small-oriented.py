"""Exact evaluation of a weak-factor example for artificial ports."""
from pathlib import Path
import json

p=Path(__file__).with_name('candidate.json')
data=json.loads(p.read_text())
witness=[1,1,2,1,1,1,1,8,10,1,1,1,1]
ports=[1,1,1,0]
e=dict(zip(data['witnesses']+data['fixed_numerals'],witness+ports))
for name,op,left,right in data['source']:
    x=e[left] if isinstance(left,str) else left
    y=e[right] if isinstance(right,str) else right
    e[name]={'+':lambda:x+y,'-':lambda:x-y,'*':lambda:x*y}[op]()
assert all(x>0 for x in witness)
assert e['q']==2 and e['R']==1 and e['k']==2
assert e['F0']==e['Fa']==1 and e['F1']==47261953 and e['Fs']==83522
assert e['P13']==3947412838465 and e['F']+e['C']>=e['q']
assert e['R']+1==2 and e['R']+2<e['q']**4
print(json.dumps({'ports':ports,'witness':witness,**{k:e[k] for k in ('q','k','G','R','F0','F1','Fa','Fs','P13')}},sort_keys=True,indent=2))
