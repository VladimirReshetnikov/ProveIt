"""Targeted hand-selected proof steps, not another search."""
import check_dag as c
import json
from pathlib import Path
D=Path(__file__).parent

def st(t):return '('+st(t[0])+'>'+st(t[1])+')' if isinstance(t,tuple) else str(t)
rows=[{'name':'LR','term':c.terms[2],'basis':'Right-implication-subterm axiom'},
      {'name':'I','term':c.terms[140],'basis':'Verified 16-node proof; leaf-instance audit reduces every L0 leaf to A=U=0'},
      {'name':'T','term':'T','basis':'Native truth code0'}]

def step(name,major,minor):
 m=next(x for x in rows if x['name']==major);n=next(x for x in rows if x['name']==minor)
 rows.append({'name':name,'term':c.cd(m['term'],n['term']),'major':major,'minor':minor})
step('R','LR','I')
step('D19','LR','R')
step('D20','LR','D19')
step('D21','D20','LR')
step('D22','D21','T')
step('D23','LR','D22')
step('D24','D23','R')
step('Peirce','D24','T')
assert rows[-1]['term']==c.terms[349]
for row in rows:row['term']=st(row['term'])
(D/'lr_only_peirce.json').write_text(json.dumps(rows,indent=2))
print(json.dumps(rows,indent=2))
