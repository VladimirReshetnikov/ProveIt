"""Exact evaluation of a weak-factor example for artificial ports."""
from pathlib import Path
import json

p=Path(__file__).with_name('candidate.json')
data=json.loads(p.read_text())
witness=[1,3,1,1,1,1,1,27,8,1,1,1,1]
ports=[2,4,0,3]
e=dict(zip(data['witnesses']+data['fixed_numerals'],witness+ports))
for name,op,left,right in data['source']:
    x=e[left] if isinstance(left,str) else left
    y=e[right] if isinstance(right,str) else right
    e[name]={'+':lambda:x+y,'-':lambda:x-y,'*':lambda:x*y}[op]()
assert all(x>0 for x in witness)
assert e['q']==3 and e['R']==1 and e['k']==2
assert e['F0']==e['Fa']==1 and e['F1']==68720812858 and e['Fs']==9150626
assert e['P13']==628838456879549107 and e['F']+e['C']>=e['q']
assert e['F']==e['q'] and e['C']==1 and ports[2]<ports[0]<=ports[3]<2*ports[0]
assert e['R']+1==2 and e['R']+2<e['q']**4
print(json.dumps({'ports':ports,'witness':witness,**{k:e[k] for k in ('q','k','G','R','F0','F1','Fa','Fs','P13')}},sort_keys=True,indent=2))
