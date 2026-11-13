#!/usr/bin/env python3
"""Freeze the AQ22/AQ17 chain and AQ16 additions over the AQ29 author parent."""
import argparse,hashlib,json,re,subprocess
from pathlib import Path
if not __debug__: raise RuntimeError('assertions required')
D=Path(__file__).resolve().parent
ROOT=D.parents[3]
BASE=D.parent/'aq17-witness-transport/author-additions.json'
assert hashlib.sha256(BASE.read_bytes()).hexdigest()=='96cd989a4abaf88c0c181e14a72946b3af1b58f4efc485a63ff1687c56918378'
parser=argparse.ArgumentParser();parser.add_argument('--source-commit',required=True);args=parser.parse_args()
assert re.fullmatch('[0-9a-f]{40}',args.source_commit)
m=json.loads(BASE.read_text());assert len(m['order'])==44 and m['status']=='FROZEN_ADDITIONS'
m['source_commit']=args.source_commit
m['scope']='Single-overlay historical author extension of audited AQ29 parent: rebuild all 44 AQ22/AQ17-chain and eight AQ16 modules; not a paired or current-source replay.'
for short in ['AdaptiveAQ16Literal','AdaptiveAQ16Zeros','AdaptiveAQ16Positive','AdaptiveAQ16Maps','AdaptiveAQ16Transport','AdaptiveAQ16','IPRAAQ16Native','IPRAStandardAQ16']:
 name='DiophantineConsistency.'+short
 p=D/'draft-src'/(short+'.lean');rel=str(p.relative_to(ROOT))
 blob=subprocess.run(['git','show',args.source_commit+':'+rel],cwd=ROOT,check=True,capture_output=True).stdout
 assert blob==p.read_bytes()
 text=blob.decode();imports=re.findall(r'^import\s+([A-Za-z_][A-Za-z0-9_.\']*)\s*$',text,re.M)
 assert len(imports)==len(set(imports))
 m['order'].append(name)
 m['sources'][name]={'workspace_path':rel,'sha256':hashlib.sha256(blob).hexdigest(),'imports':imports}
 declarations=re.findall(r'^#print axioms ([A-Za-z_][A-Za-z0-9_.\']*)\s*$',text,re.M)
 if declarations:m['axiom_reports'][name]=[name+'.'+x for x in declarations]
assert len(m['order'])==len(m['sources'])==52
out=D/'author-additions.json';out.write_text(json.dumps(m,indent=2,sort_keys=True)+'\n')
print('AQ16_FROZEN_MANIFEST',hashlib.sha256(out.read_bytes()).hexdigest())
