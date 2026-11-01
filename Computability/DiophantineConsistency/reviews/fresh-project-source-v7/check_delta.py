#!/usr/bin/env python3
"""Compare frozen source graphs and calculate declared reverse closure."""
import collections,hashlib,json
from pathlib import Path
D=Path(__file__).resolve().parent;R=D.parent;H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
files=[R/'fresh-project-closure-preflight/manifest.json',R/'fresh-project-source-v6/manifest.json',D/'manifest.json'];ms=[json.loads(x.read_text()) for x in files]
assert [H(x) for x in files]==['63b846158674d41beeaa99843d92008465f8e0fe5c45bb9e1fed4b78e1a2ab48','84bcb0021ea725056e4cfcd756ca75c52abf4a1e24a2d619a3a664aced55f6cf','914987f465c43e01cd3588921c439f90b47ace1c857d8ca0a0bd5ddaf4f90acf']
results={}
for tag,old in [('v2',ms[0]),('v6',ms[1])]:
 new=ms[2];assert old['order']==new['order'] and old['external_modules']==new['external_modules'] and set(old['sources'])==set(new['sources'])
 assert all(old['sources'][n]['imports']==new['sources'][n]['imports'] for n in old['sources'])
 changed=sorted(n for n in old['sources'] if old['sources'][n]['sha256']!=new['sources'][n]['sha256']);reverse=collections.defaultdict(set)
 for name,row in new['sources'].items():
  for dep in row['imports']:
   if dep in new['sources']:reverse[dep].add(name)
 affected=set(changed);todo=changed[:]
 while todo:
  for n in reverse[todo.pop()]-affected:affected.add(n);todo.append(n)
 assert new['target'] in affected
 results[tag]={'changed':changed,'affected_count':len(affected),'affected':sorted(affected)}
assert results['v2']['affected_count']==197 and results['v6']['affected_count']==121
out={'status':'PASS_STATIC_GRAPH_COMPARISON','inputs_sha256':{str(x):H(x) for x in [Path(__file__).resolve(),*files]},'results':results,'scope':'Source-declared graph comparison only; not an object reuse or Lean compilation proof.'};p=D/'delta.json';assert not p.exists();p.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n');print(out['status'],H(p))
