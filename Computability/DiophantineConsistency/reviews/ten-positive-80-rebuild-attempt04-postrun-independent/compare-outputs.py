#!/usr/bin/env python3
"""Compare checked fresh stage objects with original plan object hashes, not producer ancestry."""
from pathlib import Path
from hashlib import sha256
import json
D=Path(__file__).resolve().parents[2];P=D/'reviews/ten-positive-80-127-rebuild-preflight/observations/attempt01.json';R=D/'research/ten-positive-80-coherent-rebuild/observations/attempt04/result.json'
def sha(p):return sha256(Path(p).read_bytes()).hexdigest()
p=json.loads(P.read_text());r=json.loads(R.read_text());assert r['status']=='PASS' and len(r['stages'])==127
same=[];different=[]
for s in r['stages']:
 n=s['module'];old=p['sources'][n]['selected_object']['sha256'];new=s['output']['.olean']['sha256'];assert sha(s['output']['.olean']['path'])==new
 (same if old==new else different).append((n,old,new))
assert len(same)==122 and len(different)==5
print('PASS 127 fresh output bytes: 122 match selected prior object hashes; 5 differ')
for n,a,b in different:print(n,'old',a,'new',b)
print('Matching bytes alone do not prove identical producer-time dependencies.')
print('plan',sha(P),'result',sha(R))
