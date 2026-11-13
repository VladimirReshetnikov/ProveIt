#!/usr/bin/env python3
"""Generate a compact prefix representation of pinned external seed rows."""
import hashlib,json
from pathlib import Path
P=Path(__file__).resolve().parent
src=P.parent/'nine-sharing-sign14-tau-candidate/seed.json'
raw=src.read_bytes();assert hashlib.sha256(raw).hexdigest()=='7048a10d409ab5ff8031a444cd32117ba772b3834425c17a066188338e189ea9'
s=json.loads(raw);ports={'beta':'B','K0':'K','MC':'C','MF':'F'}
def enc(t):
 op=t[0]
 if op=='var': assert 0<=t[1]<15;return chr(ord('a')+t[1]),1
 if op=='port':return ports[t[1]],1
 if op=='num': assert t[1] in (1,2,3,4);return str(t[1]),1
 assert op in ('add','sub','mul') and len(t)==3
 a,da=enc(t[1]);b,db=enc(t[2]);return {'add':'+','sub':'-','mul':'*'}[op]+a+b,1+max(da,db)
rows=[]
for i,r in enumerate(s['residuals']):
 data,depth=enc(r['expr']);rawrow=data.encode('ascii');p=P/f'row{i:02}.prefix';p.write_bytes(rawrow)
 rows.append({'gate':r['gate'],'file':p.name,'length':len(rawrow),'sha256':hashlib.sha256(rawrow).hexdigest(),'depth':depth})
(P/'manifest.json').write_text(json.dumps({'source_sha256':hashlib.sha256(raw).hexdigest(),'ports':['beta','K0','MC','MF'],'rows':rows},sort_keys=True,indent=2)+'\n')
print(json.dumps({'status':'GENERATED','rows':rows},sort_keys=True))
