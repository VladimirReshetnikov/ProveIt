"""Owned fixed five-node native proof, not another formula-search pilot."""
import json
from pathlib import Path
OUT=Path(__file__).parent
def P(a,b):return (a+b)*(a+b+1)//2+b
def I(a,b):return 4*P(a,b)
def R(a,b):return I(a,b)+1
def L(a,b,c,u):return I(I(I(c,u),a),I(I(a,c),I(b,c)))
def HB(a,b,c):return L(a,b,c,b)
def HR(a,b,c):return L(a,b,c,R(b,c))
x=21523360;t=I(0,40);identity=I(t,t)
rows=[{'id':1,'axiom':'H_B','args':[1,0,0],'code':HB(1,0,0)},
      {'id':2,'axiom':'H_Rbc','args':[40,0,0],'code':HR(40,0,0)},
      {'id':3,'major':2,'minor':1,'code':x},
      {'id':4,'axiom':'H_B','args':[0,0,40],'code':HB(0,0,40)},
      {'id':5,'major':4,'minor':3,'code':identity}]
for row in rows:
    if 'major' in row:
        assert row['major']<row['id'] and row['minor']<row['id']
        assert rows[row['major']-1]['code']==I(rows[row['minor']-1]['code'],row['code'])
assert t==3440
result={'status':'PASS_FIXED_NATIVE_IDENTITY','identity_argument':t,'identity_code':identity,
        'axioms':3,'MP_steps':2,'nodes':rows,'formula_search':False,
        'scope':'A particular identity instance, not uniform identity, K/S or reverse calibration.'}
(OUT/'FIXED_IDENTITY_RECEIPT.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:v for k,v in result.items() if k!='nodes'},indent=2))
