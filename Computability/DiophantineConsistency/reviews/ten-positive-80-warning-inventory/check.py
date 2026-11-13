#!/usr/bin/env python3
"""Inventory retained producer diagnostics for the planned 127 stages."""
from hashlib import sha256
from pathlib import Path
import json,re
H=Path(__file__).resolve().parent;D=H.parents[1]
PLAN=D/'reviews/ten-positive-80-127-rebuild-preflight/observations/attempt01.json'
SINGLE=D/'reviews/ten-positive-80-fixed-ipra-serialized-closure/observations/producer-audit01.json'
NINE=D/'reviews/ten-positive-80-nine-prefix-producer-audit/observations/attempt01.json'
ADAPT=D/'reviews/ipra-adaptive-native-fixed-continuation-verification-peer/author-state.json'
HA=D/'reviews/ha87-isolated-full-author-pass/state.json';OUT=H/'observations/attempt01.json'
def sha(p):return sha256(Path(p).read_bytes()).hexdigest()
def need(b,m):
 if not b:raise RuntimeError(m)
need(not OUT.exists(),'output exists')
p=json.loads(PLAN.read_text());single=json.loads(SINGLE.read_text());nine=json.loads(NINE.read_text());ad=json.loads(ADAPT.read_text());ha=json.loads(HA.read_text())
adaptive={r['name']:r for r in ad['records']};hr={r['module']:r for r in ha['records']};rows={};known=[];not_inventoried=[]
for i,n in enumerate(p['ordered'],1):
 if n in single['matched']:
  f=Path(single['matched'][n]['receipt']);need(sha(f)==single['matched'][n]['receipt_sha256'],'receipt drift '+n);d=json.loads(f.read_text())
  outputs=[]
  for key in ('stdout','stderr'):
   path=f.parent/key;need(path.is_file() and sha(path)==d[key+'_sha256'],'log drift '+n+' '+key);outputs.append(path.read_text())
  hits=re.findall(r'(?i)\b(?:error|warning)(?:\([^:\n]*\))?:',''.join(outputs))
  rows[n]={'index':i,'kind':'single','receipt':str(f),'diagnostic_markers':hits}
  if hits:known.append(n)
 elif n in nine['cases']:
  rec=nine['cases'][n];policy=rec.get('warning_policy');rows[n]={'index':i,'kind':'nine-prefix','receipt':rec['receipt'],'warning_policy':policy}
  if policy:known.append(n)
 elif n in adaptive:
  rec=adaptive[n];rows[n]={'index':i,'kind':'adaptive-peer-author','warnings':rec.get('warnings',[])}
  if rec.get('warnings'):known.append(n)
 elif n in hr:
  rec=hr[n];rows[n]={'index':i,'kind':'ha87-author','warning_lines':rec.get('warning_lines',[])}
  if rec.get('warning_lines'):known.append(n)
 else:not_inventoried.append(n)
result={'status':'INVENTORY','inputs':{str(f):sha(f) for f in (PLAN,SINGLE,NINE,ADAPT,HA)},'rows':rows,
        'historically_reported_diagnostics':known,'not_inventoried':not_inventoried,
        'scope':'historical producer log/policy inventory only; no warning exception or prediction for fresh builds'}
OUT.parent.mkdir(parents=True,exist_ok=True);OUT.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
print(json.dumps({'status':'INVENTORY','modules':len(p['ordered']),'inventoried':len(rows),
                  'historically_reported_diagnostics':known,'not_inventoried':not_inventoried,'sha256':sha(OUT)},sort_keys=True))
