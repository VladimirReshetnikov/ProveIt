import json,re
from pathlib import Path
from hashlib import sha256
base=Path('research/ten-positive-80-bfs-full-closure');o=base/'observations/producers01'
def sha(p):return sha256(Path(p).read_bytes()).hexdigest()
t=json.loads((o/'terminal.json').read_text());assert t['exit']==0 and sha(base/'audit-producers.py')==t['script_sha256']=='b11b02890eff5bbf7dd52e4a280af77e8c86e2b818dcc6dd0e04060e59a18b8b'
assert sha(o/'stdout')==t['stdout_sha256']=='21c012d589b30c78035ccad1ecf8754ad2fb590bd4dc1b2d32fdff20f372ba27' and sha(o/'stderr')==t['stderr_sha256'] and not (o/'stderr').read_text()
capture=base/'observations/attempt01/result.json';assert sha(capture)=='1b41178b0123d25e8814b6d430c1f996c90765fc5f1517283d4248b787dc6e1b';c=json.loads(capture.read_text());j=json.loads((o/'stdout').read_text());assert j['status']=='PASS' and len(j['modules'])==12 and {x['module'] for x in j['modules']}==set(c['new_project'])
edges=0
for m in j['modules']:
 n=m['module'];p=Path(m['receipt']);assert sha(p)==m['receipt_sha256'];r=json.loads(p.read_text());v=c['closure']['project'][n];assert r['status']=='PASS' and r['exit']==0 and r['reason'] is None
 assert r['output']==v['path'] and r['output_sha256']==v['record']['sha256']==sha(r['output'])
 source=Path(m['source']);sp=r['pins'][str(source)];assert sha(source)==m['source_sha256']==sp['sha256']==r['source_sha256'] and str(source.resolve())==sp['resolved']
 imports=re.findall(r'^import\s+(\S+)',source.read_text(),re.M);assert imports==[i for i in v['imports'] if i!='Init']==[x['module'] for x in m['direct_imports']]
 for x in m['direct_imports']:
  d=c['closure']['project'][x['module']];pin=r['pins'][x['path']];assert x['path']==d['path'] and x['sha256']==pin['sha256']==d['record']['sha256']==sha(x['path']) and x['resolved']==pin['resolved']==d['record']['resolved']==str(Path(x['path']).resolve());edges+=1
 for stream in ['stdout','stderr']:
  assert sha(p.parent/stream)==r[stream+'_sha256']
print('PASS: 12 retained producer receipts, output/source hashes, serialized direct import lists and 16 direct project-object pin edges matched; current source and object bytes rehashed.')
assert edges==j['project_direct_edges']==16
print('Retained producer pins are not per-edge independent kernel replay or a complete producer-time companion/lookup/package/transitive provenance certificate.')
