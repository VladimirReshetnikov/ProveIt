#!/usr/bin/env python3
"""Freeze the AQ22 chain and AQ17 additions over the audited AQ29 author."""
import hashlib,json,re,subprocess
from pathlib import Path
if not __debug__: raise RuntimeError('assertions required')
D=Path(__file__).resolve().parent
ROOT=D.parents[3]
BASE=D.parent/'adaptive-aq22-proof/author-additions.json'
COMMIT='1eae3a0a882e8bba1ee0fecc6461dd1f0602d06d'
assert hashlib.sha256(BASE.read_bytes()).hexdigest()=='3c5df040f94803b19ccbed14ec93be2e3de2e16ed9c31efd9bcfb531373200df'
m=json.loads(BASE.read_text());assert len(m['order'])==37 and m['status']=='FROZEN_ADDITIONS'
m['source_commit']=COMMIT
m['scope']='Single-overlay historical author extension of audited AQ29 parent: rebuild all 37 AQ22-chain and seven AQ17 modules; not a paired or current-source replay.'
for short in ['AdaptiveAQ17Literal','AdaptiveAQ17Zeros','AdaptiveAQ17Maps','AdaptiveAQ17Transport','AdaptiveAQ17','IPRAAQ17Native','IPRAStandardAQ17']:
 name='DiophantineConsistency.'+short
 p=D/'draft-src'/(short+'.lean');rel=str(p.relative_to(ROOT))
 blob=subprocess.run(['git','show',COMMIT+':'+rel],cwd=ROOT,check=True,capture_output=True).stdout
 assert blob==p.read_bytes()
 text=blob.decode();imports=re.findall(r'^import\s+([A-Za-z_][A-Za-z0-9_.\']*)\s*$',text,re.M)
 assert len(imports)==len(set(imports))
 m['order'].append(name)
 m['sources'][name]={'workspace_path':rel,'sha256':hashlib.sha256(blob).hexdigest(),'imports':imports}
 declarations=re.findall(r'^#print axioms ([A-Za-z_][A-Za-z0-9_.\']*)\s*$',text,re.M)
 if declarations:m['axiom_reports'][name]=[name+'.'+x for x in declarations]
assert len(m['order'])==len(m['sources'])==44
out=D/'author-additions.json';out.write_text(json.dumps(m,indent=2,sort_keys=True)+'\n')
print('AQ17_FROZEN_MANIFEST',hashlib.sha256(out.read_bytes()).hexdigest())
