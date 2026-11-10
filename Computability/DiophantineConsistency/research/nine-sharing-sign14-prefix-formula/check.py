#!/usr/bin/env python3
"""Check exact prefix decoding and hashes against the external seed AST."""
import hashlib,json
from pathlib import Path
P=Path(__file__).resolve().parent;src=P.parent/'nine-sharing-sign14-tau-candidate/seed.json'
h=lambda b:hashlib.sha256(b).hexdigest();raw=src.read_bytes();manifest=json.loads((P/'manifest.json').read_text())
assert h(raw)==manifest['source_sha256']=='7048a10d409ab5ff8031a444cd32117ba772b3834425c17a066188338e189ea9'
seed=json.loads(raw);assert manifest['ports']==['beta','K0','MC','MF'] and len(manifest['rows'])==len(seed['residuals'])==5
ports={'B':'beta','K':'K0','C':'MC','F':'MF'};ops={'+':'add','-':'sub','*':'mul'}
def dec(s,i):
 assert i<len(s);c=s[i];i+=1
 if c in ops:
  a,i=dec(s,i);b,i=dec(s,i);return [ops[c],a,b],i
 if c in ports:return ['port',ports[c]],i
 if c in '1234':return ['num',int(c)],i
 assert 'a'<=c<='o';return ['var',ord(c)-ord('a')],i
for row,expected in zip(manifest['rows'],seed['residuals']):
 data=(P/row['file']).read_bytes();assert len(data)==row['length'] and h(data)==row['sha256'];assert row['gate']==expected['gate']
 tree,end=dec(data.decode('ascii'),0);assert end==len(data) and tree==expected['expr']
print('PASS: all five prefix rows decode exactly to pinned external seed AST rows')
