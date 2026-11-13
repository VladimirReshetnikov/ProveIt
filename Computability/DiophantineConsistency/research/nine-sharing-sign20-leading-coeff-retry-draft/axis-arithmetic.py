#!/usr/bin/env python3
"""Independent external-AST weighted/bivariate check, no Lean binding."""
import hashlib, json
from pathlib import Path
p = Path(__file__).resolve().parent.parent / 'nine-sharing-sign20-degree20-e-candidate/seed.json'
b = p.read_bytes()
assert hashlib.sha256(b).hexdigest() == '2593aca2ac701ff9312fe5aff1719bbf4fd29a97e2c3e14642bf137d6ef8bf7d'
s = json.loads(b)
axis = {1, 9, 11, 15}
def degree(e):
    op=e[0]
    if op=='var':return int(e[1] in axis)
    if op in ('num','port'):return 0
    a,b=degree(e[1]),degree(e[2])
    return a+b if op=='mul' else max(a,b)
def add(a,b,sign=1):
    c=a.copy()
    for k,v in b.items():c[k]=c.get(k,0)+sign*v
    return {k:v for k,v in c.items() if v}
def poly(e):
    op=e[0]
    if op=='num':return {(0,0):e[1]} if e[1] else {}
    if op=='var':return {(1,0):1} if e[1] in axis else {}
    if op=='port':
        assert e[1]=='beta'
        return {(0,1):1}
    a,b=poly(e[1]),poly(e[2])
    if op=='add':return add(a,b)
    if op=='sub':return add(a,b,-1)
    assert op=='mul'
    c={}
    for (i,j),x in a.items():
        for (k,l),y in b.items():c[(i+k,j+l)]=c.get((i+k,j+l),0)+x*y
    return {k:v for k,v in c.items() if v}
degrees={row['gate']:degree(row['expr']) for row in s['residuals']}
assert degrees=={'Y':3,'main_root':5,'Dc2':10,'tau':4,'N0':10,'Nt':2,
                 'cTminusR':4,'V':2,'V2minusY2':0,'Na':0,'scaled_Ns':6}
for gate in ('Dc2','N0'):
    row,=[r for r in s['residuals'] if r['gate']==gate]
    z=poly(row['expr'])
    assert {k:v for k,v in z.items() if k[0]>=10}=={(10,2):-1}
print(json.dumps({'status':'PASS_EXTERNAL_AXIS','degrees':degrees,
                  'Dc2_t10':'-beta^2','N0_t10':'-beta^2',
                  'scope':'external AST only; no Lean binding or theorem'},sort_keys=True))
