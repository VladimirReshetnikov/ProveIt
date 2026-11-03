#!/usr/bin/env python3
"""Independently evaluate one finite candidate point; no Lean or counterexample."""
from pathlib import Path
from hashlib import sha256
import json
D=Path(__file__).resolve().parents[2]; P=D/'research/trace74-boundary-seed-probe'; G=D/'research/trace74-mask-coordinate-probe/candidate.json'
raw=G.read_bytes();assert sha256(raw).hexdigest()=='dafefaa40173c9f75c414171896e19ddcf5f5eec82a0612d82a4e23988ee7353';g=json.loads(raw)
inputs={'J':1,'F':1,'C':1,'i':1,'T':1,'w':7,'s':1,'n':1,'eta':1187,'zeta':5985,'beta':1,'K0':0,'MC':0,'MF':0}
assert all(inputs[x]>0 for x in g['witnesses']) and all(inputs[x]>=0 for x in g['fixed_numerals'])
r=dict(inputs);assert len(g['source'])==74
for out,op,a,b in g['source']:
 assert out not in r and op in '+-*'
 a=a if type(a)==int else r[a];b=b if type(b)==int else r[b]
 if op=='+':x=a+b
 elif op=='-':x=a-b
 else:x=a*b
 r[out]=x
assert (r['q'],r['X'],r['Y'],r['k'],r['c'],r['R'])==(2,14,8,7172,58563,3)
P0=r['X']*r['Y']**2;assert P0==896 and r['q']-inputs['F']-inputs['C']==0 and inputs['F']+inputs['C']==r['q']
tau=2*(2*P0+1)**2-1;assert tau==6429697 and r['k']==4*(2*P0+1) and r['Dtau']==tau**2==1+P0*(P0+1)*r['k']**2
assert r['c']==4*(r['X']*r['Y']+r['Y']+1)**2-1 and 0<inputs['eta']<r['k']
assert r['N']!=0 and not (0<inputs['MC']<inputs['beta'])
print('PASS 74 rows; exact graph output nonzero; SHA-256 signed decimal',sha256(str(r['N']).encode()).hexdigest())
print('partial first-index=2 and main-index=3 constraints hold; guard equality fails; chosen ports violate fixed-port MC bound; no positive-zero or fixed-port counterexample')
