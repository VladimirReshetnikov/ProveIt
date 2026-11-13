from pathlib import Path
from hashlib import sha256
import json,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path('research/ordinary13-eta85-zeta-zero-boundary-audit')
oldpath=Path('research/ordinary13-eta-zero-graph-adapter-audit/prototype.json')
oldbytes=oldpath.read_bytes(); old=json.loads(oldbytes);rows=[]
for row in old['source']:
 if row==['k','+','kbase',1]:continue
 if row==['r0','-','kbase','R']:
  rows.extend([['r0base','-','kbase','R'],['r0','-','r0base',1]])
 else:rows.append([('kbase' if x=='k' else x) for x in row])
new={'name':'eta/zeta-natural boundary probe; not a proved reduction',
 'domain':old['domain'],'witnesses':old['witnesses'],'fixed_numerals':old['fixed_numerals'],
 'source':rows,'output':old['output'],'parent_sha256':sha256(oldbytes).hexdigest(),
 'proof_status':'structural zeta-unshift probe only; no compact zero map or endpoint'}
b=(json.dumps(new,indent=2,ensure_ascii=False)+'\n').encode();target=D/'probe.json'
if '--write' in sys.argv:target.write_bytes(b)
else:assert target.read_bytes()==b
print(json.dumps({'parent_sha256':sha256(oldbytes).hexdigest(),'probe_sha256':sha256(b).hexdigest(),'old_rows':len(old['source']),'probe_rows':len(rows),'lean_executed':False},sort_keys=True,indent=2))
