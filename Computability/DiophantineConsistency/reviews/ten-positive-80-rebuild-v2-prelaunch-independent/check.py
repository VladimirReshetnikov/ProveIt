#!/usr/bin/env python3
"""Read-only source-plan/static guard review, never launches Lean or rebuild."""
from pathlib import Path
from hashlib import sha256
import json,re,subprocess,sys
D=Path(__file__).resolve().parents[2];R=D/'reviews';S=D/'research/ten-positive-80-coherent-rebuild/run-v2.py'; P=R/'ten-positive-80-127-rebuild-preflight/observations/attempt01.json';C=R/'ten-positive-80-fixed-ipra-serialized-closure/observations/attempt01/result.json';H=R/'ten-positive-80-ha87-producer-drift/observations/attempt01.json'
def sha(p):return sha256(Path(p).read_bytes()).hexdigest()
def j(p):return json.loads(Path(p).read_text())
assert sha(S)=='b5d1c48634b9fb78c0c543c2523537ea71225b1dea9906d4fc5faee6efb6bc2a'
assert sha(P)=='cd224b6f17f9cd3cd08cf3a9e84923c1de9edbb635f6969cd4e1991e009b7e3a' and sha(C)=='d65d7c776eb23425f9e2a290d8c3fdeebc011920619241290fdee85bc4ae68a9'
p,c,h=j(P),j(C),j(H);order=p['ordered'];assert p['status']=='PASS_PLAN_ONLY' and c['status']=='PASS' and len(order)==len(set(order))==127 and set(order)==set(p['sources'])==set(h['affected']) and order[-1]=='Direct80SymbolicFixedIPRA'
position={n:i for i,n in enumerate(order)}
for n in order:
 z=p['sources'][n];f=Path(z['source']);assert sha(f)==z['sha256'] and z['selected_object']==c['project'][n]['selected']
 imports=[m for line in f.read_text().splitlines() if line.startswith('import ') for m in line[7:].split()]
 assert set(imports)==set(z['imports'])==set(c['fresh_headers'][n])-{ 'Init' }
 assert all(d not in position or position[d]<position[n] for d in imports)
for path,digest in p['inputs'].items():assert sha(path)==digest
s=S.read_text();assert "s['mem_available_kib']<2*1024**2" in s and "before['mem_available_kib']>=8*1024**2" in s
warn=re.compile(r'(?i)(?:error:|warning:|sorryAx)');assert warn.search('warning: plain') and not warn.search('warning(lean.unusedSimpArgs): coded') and not warn.search('error(lean.foo): coded')
assert "obs=H/'observations'/arg.attempt" in s and "tempfile.mkdtemp(prefix='direct80-coherent-rebuild-')" in s
subprocess.run([sys.executable,'-I','-S','-B',str(R/'ten-positive-80-ha87-drift-independent/check.py')],check=True,stdout=subprocess.DEVNULL)
print('PASS source plan: 127 current source hashes/import headers, topological order and prior 127 drift cone')
print('HOLD v2: monitor permits 2–8 GiB available; diagnostic regex misses coded warning/error examples')
print('No Lean/rebuild run. External package history remains outside plan; see README for further guard gaps.')
