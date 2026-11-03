#!/usr/bin/env python3
"""Exact first-factor zero whose 86 forward lift is negative."""
from pathlib import Path
from hashlib import sha256
import json
p=Path(__file__).resolve().parent.parent/'ordinary12-absorb89-probe/graph-dag.json'
if sha256(p.read_bytes()).hexdigest()!='280b23e5be95692b9db0183affce4247d974320ded1e709f41b05cc7e32b2fdd':raise RuntimeError('parent graph drift')
g=json.loads(p.read_text());v={i:i for i in range(5)}
v.update({k:1 for k in g['witnesses']+g['fixed_numerals']})
v.update(beta=3,K0=3751,MC=0,MF=0,r=4489)
for n,op,x,y in g['source']:
 a,b=v[x],v[y];v[n]=a+b if op=='+' else a-b if op=='-' else a*b
out={k:v[k] for k in ['q','qm','X','Y','ell','k','Bt','Z','A0','A1','N']}
out['r_new']=v['ell']+v['k']+v['r']-v['k']*v['Bt']
expected={'q':4,'qm':3,'X':4,'Y':64,'ell':32768,'k':2,'Bt':30012,'Z':-98307,'A0':0,'A1':107467408507521,'N':1339555313198018361550984423709760,'r_new':-22765}
if out!=expected:raise RuntimeError('unexpected evaluation')
print(json.dumps(out,sort_keys=True))
