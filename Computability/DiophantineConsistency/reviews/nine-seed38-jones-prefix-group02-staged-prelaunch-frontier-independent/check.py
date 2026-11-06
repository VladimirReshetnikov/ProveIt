#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
d=Path(__file__).resolve().parents[2];p=d/'research/nine-seed38-jones-prefix-group02-staged-check'
def h(q):return hashlib.sha256(q.read_bytes()).hexdigest()
for n,v in {'run.py':'39b52d5c25ac7a0506dd0392dc5016ec1625428fe72c1e3a2fe36d9da8a3dfbd','provider_preflight.py':'abea5c2527ce77672dc76e28941ffa00608e05c7c4c44bb2eeab3e20643cfe73','source-manifest.json':'8ac95074a55c6e9335d5e1a977a7f0f19a04ce259897b10568229a190c6f6ac4'}.items():assert h(p/n)==v
rows=json.loads((p/'source-manifest.json').read_text())['rows']
expected=[('Norm38MacroPrefixCarry','7d99a72b7c27c335f4e8c0f2e5a66468c907c8321dce03259a4e13cd456e2d3e','Norm38MacroPrefixGroup01',['d4_B','d5_B','d6_B']),('Norm38MacroPrefixE','c29dd4f792f6120f11d94cd0ccb1e20524219e01357ade3a3f7e56f970216868','Norm38MacroPrefixCarry',['prefix_e']),('Norm38MacroPrefixEll','e98e9d78074b1eace78fb798278b7624839d768c0c25717b0e32f78e24277c01','Norm38MacroPrefixCarry',['prefix_ell']),('Norm38MacroPrefixLambda','8d81e80eb986a42ede2ab0736bc1d458c4cb73d3b3895b83837a00c480087861','Norm38MacroPrefixCarry',['prefix_lambda'])]
assert len(rows)==len(expected)
for row,(n,sha,imp,theorems) in zip(rows,expected):
 q=p/'src/DiophantineConsistency'/f'{n}.lean';assert h(q)==sha==row['source_sha256'];s=q.read_text();assert row['module']=='DiophantineConsistency.'+n;assert row['imports']==re.findall(r'^import ([\w.]+)$',s,re.M)==['DiophantineConsistency.'+imp];assert re.findall(r'^theorem (\w+)',s,re.M)==theorems;assert re.findall(r'^#print axioms (\w+)',s,re.M)==theorems
r=subprocess.run([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],capture_output=True,text=True,check=True);o=json.loads(r.stdout);assert o['status']=='PASS_NO_LEAN_PREFLIGHT' and o['stage_count']==4
print(json.dumps({'status':'PASS','preflight':o,'scope':'uncompiled symbolic short-prefix statements; no Lean replay'},sort_keys=True,indent=2))
