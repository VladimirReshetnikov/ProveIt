#!/usr/bin/env python3
"""Check the short-fragment DAG reconstructs all five audited prefix rows."""
import hashlib,json
from pathlib import Path
P=Path(__file__).resolve().parent;h=lambda b:hashlib.sha256(b).hexdigest();m=json.loads((P/'manifest.json').read_text());seed=(P.parent/'nine-sharing-sign14-tau-candidate/seed.json').read_bytes()
assert h(seed)==m['seed_sha256']=='7048a10d409ab5ff8031a444cd32117ba772b3834425c17a066188338e189ea9'
frags=[]
for i,r in enumerate(m['fragments']):
 assert r['file']==f'fragment{i:03}.prefix';b=(P/r['file']).read_bytes();assert 1<=len(b)<=32 and len(b)==r['length'] and h(b)==r['sha256'];frags.append(b)
assert len(m['shared'])==44 and len(m['rows'])==5
def materialize(node,bound):
 tag=node[0]
 if tag=='frag':assert len(node)==2 and 0<=node[1]<len(frags);return frags[node[1]]
 if tag=='ref':assert len(node)==2 and 0<=node[1]<bound;return materialize(m['shared'][node[1]],node[1])
 assert tag=='op' and len(node)==4 and node[1] in '+-*';return node[1].encode('ascii')+materialize(node[2],bound)+materialize(node[3],bound)
for i,node in enumerate(m['shared']):materialize(node,i)
for i,node in enumerate(m['rows']):assert materialize(node,44)==(P.parent/'nine-sharing-sign14-prefix-formula'/f'row{i:02}.prefix').read_bytes()
print('PASS: acyclic short-fragment DAG reconstructs all five pinned prefix rows')
