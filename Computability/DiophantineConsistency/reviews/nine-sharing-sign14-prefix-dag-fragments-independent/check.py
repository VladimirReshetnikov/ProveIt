#!/usr/bin/env python3
import hashlib,json,sys,subprocess
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];p=root/'research/nine-sharing-sign14-prefix-dag-fragments';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest();assert sha(p/'manifest.json')=='19558421ef6ce10151450614213cfb90789b0cd1407ada737e5d97049a94224d' and sha(p/'check.py')=='09828ae207c99968e2ee093ad42fbbd66a6223b67df5e46d14ac0615cceb657b'
m=json.loads((p/'manifest.json').read_text());assert m['seed_sha256']==sha(root/'research/nine-sharing-sign14-tau-candidate/seed.json')=='7048a10d409ab5ff8031a444cd32117ba772b3834425c17a066188338e189ea9';assert len(m['fragments'])==29 and len(m['shared'])==44 and len(m['rows'])==5
frags=[]
for i,e in enumerate(m['fragments']):
 q=p/f'fragment{i:03}.prefix';b=q.read_bytes();assert e['file']==q.name and e['length']==len(b) and e['sha256']==sha(q) and 1<=len(b)<=32 and all(x<128 for x in b);frags.append(b)
assert len(set(frags))==29
shared=[]
def expand(node,bound):
 assert isinstance(node,list)
 if node[0]=='frag':assert len(node)==2 and type(node[1])==int and 0<=node[1]<len(frags);return frags[node[1]]
 if node[0]=='ref':assert len(node)==2 and type(node[1])==int and 0<=node[1]<bound;return shared[node[1]]
 assert node[0]=='op' and len(node)==4 and node[1] in ('+','-','*');return node[1].encode()+expand(node[2],bound)+expand(node[3],bound)
for i,node in enumerate(m['shared']):shared.append(expand(node,i))
for i,node in enumerate(m['rows']):assert expand(node,44)==(root/'research/nine-sharing-sign14-prefix-formula'/f'row{i:02}.prefix').read_bytes()
for f in ('nine-sharing-sign14-prefix-formula-independent',):subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews'/f/'check.py')],capture_output=True,check=True,timeout=120)
x=subprocess.run([sys.executable,'-I','-S','-B',str(p/'check.py')],capture_output=True,text=True,check=True,timeout=120);assert not x.stderr and x.stdout.strip()=='PASS: acyclic short-fragment DAG reconstructs all five pinned prefix rows'
print(json.dumps({'status':'PASS_EXTERNAL_AUDIT','fragments':29,'shared':44,'rows':5,'scope':'external fragment DAG materialization only; no Lean full-file/JSON/PDF theorem'},indent=2))
