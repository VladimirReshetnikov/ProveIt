#!/usr/bin/env python3
"""Check captured warning inventory and 127 plan without Lean execution."""
from pathlib import Path
from hashlib import sha256
from collections import Counter
import json,re,subprocess,sys
D=Path(__file__).resolve().parents[2];R=D/'reviews';F=R/'ten-positive-80-warning-inventory/observations/attempt01.json';P=R/'ten-positive-80-127-rebuild-preflight/observations/attempt01.json';S=R/'ten-positive-80-fixed-ipra-serialized-closure/observations/producer-audit01.json';N=R/'ten-positive-80-nine-prefix-producer-audit/observations/attempt01.json';A=R/'ipra-adaptive-native-fixed-continuation-verification-peer/author-state.json';H=R/'ha87-isolated-full-author-pass/state.json'
def sha(p):return sha256(Path(p).read_bytes()).hexdigest()
def j(p):return json.loads(Path(p).read_text())
i,p,s,n,a,h=map(j,(F,P,S,N,A,H));assert sha(F)=='7e96b3fb0edf597d0e63097d2e66295f27dd6adf7b537a9c869ad60d5a356871'
for path,digest in i['inputs'].items():assert sha(path)==digest
assert i['status']=='INVENTORY' and len(p['ordered'])==127 and set(i['rows'])==set(p['ordered']) and not i['not_inventoried']
adaptive={r['name']:r for r in a['records']};ha={r['module']:r for r in h['records']};known=[];counts=Counter()
for idx,name in enumerate(p['ordered'],1):
 z=i['rows'][name];assert z['index']==idx;counts[z['kind']]+=1
 if z['kind']=='single':
  it=s['matched'][name];f=Path(it['receipt']);assert str(f)==z['receipt'] and sha(f)==it['receipt_sha256'];r=j(f);assert r['exit']==0 and r['reason'] is None
  text=''
  for part in ('stdout','stderr'):
   q=f.parent/part;assert sha(q)==r[part+'_sha256'];text+=q.read_text()
  markers=re.findall(r'(?i)\b(?:error|warning)(?:\([^:\n]*\))?:',text);assert markers==z['diagnostic_markers']
  if markers:known.append(name)
 elif z['kind']=='nine-prefix':
  case=n['cases'][name];r=j(case['receipt']);assert z['receipt']==case['receipt'] and sha(case['receipt'])==case['receipt_sha256'] and z['warning_policy']==case['warning_policy']==r.get('warning_policy')
  if z['warning_policy']:
   pol=z['warning_policy'];assert pol['module']==name and pol['source_sha256']==p['sources'][name]['sha256'];known.append(name)
 elif z['kind']=='adaptive-peer-author':
  assert z['warnings']==adaptive[name].get('warnings',[])
  if z['warnings']:known.append(name)
 elif z['kind']=='ha87-author':
  assert z['warning_lines']==ha[name].get('warning_lines',[])
  if z['warning_lines']:known.append(name)
 else:raise AssertionError(z)
assert counts==Counter({'single':110,'adaptive-peer-author':7,'ha87-author':5,'nine-prefix':5})
assert known==i['historically_reported_diagnostics'] and [(p['ordered'].index(n)+1,n) for n in known]==[(3,'DiophantineConsistency.ArithmeticPellPigeonhole'),(5,'DiophantineConsistency.ModelArithmetic'),(13,'DiophantineConsistency.ModelRatioBounds')]
subprocess.run([sys.executable,'-I','-S','-B',str(R/'ten-positive-80-rebuild-v2-prelaunch-independent/check.py')],check=True,stdout=subprocess.DEVNULL)
print('PASS 127 source plan/topology; 110 single receipt logs, 5 nine-prefix policy fields, 7 adaptive fields, 5 HA87 fields')
print('Historical diagnostics recorded at stages 3, 5, 13; no inference about unspecified raw logs or fresh-run output.')
print('inventory',sha(F),'plan',sha(P),'No Lean replay or warning authorization')
