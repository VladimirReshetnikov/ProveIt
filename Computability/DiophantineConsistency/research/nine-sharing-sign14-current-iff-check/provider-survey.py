#!/usr/bin/env python3
import hashlib,json
from pathlib import Path
D=Path(__file__).resolve().parents[2]
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def need(x,m):
 if not x:raise RuntimeError(m)
state=D/'research/nine-sharing-sign33-current-windows-check/attempt01/state.json';checker=D/'reviews/nine-sharing-sign33-current-windows-terminal-frontier-independent/check.py'
need(sha(state)=='ed0ee11bdf097d8d844da870cd9c2191f861d7e7f5e23bdf53114648f1bf64db','state drift');need(sha(checker)=='2d4993bdfa3ad0e162f9a14868996160122959d1cb6edcbabbfdabf8c3283933','audit checker drift');s=json.loads(state.read_text());need(s['status']=='PASS' and len(s['rows'])==1,'state status');r=s['rows'][0];need(r['module']=='Sign33CurrentWindows' and r['deps']['exit']==0 and r['compile']['exit']==0,'stage')
d=r['dependencies']['DiophantineConsistency.ArithmeticCarrierSoundness2011'];need(r['direct_guard'][d['path']]=={'realpath':d['realpath'],'sha256':d['sha256']},'historic direct guard');need(d['sha256']=='fbcc145628f84d5937737fa25338a1c03098ccc228f03a9967b6691acbc096ab','object hash')
for q in [Path(d['path']),Path('/tmp/nine-sharing-sign14-seed-iff-check-20261110/lib/DiophantineConsistency/ArithmeticCarrierSoundness2011.olean')]:need(q.is_file() and str(q.resolve())==d['realpath'] and sha(q)==d['sha256'],'current provider drift')
print(json.dumps({'status':'PASS','realpath':d['realpath'],'sha256':d['sha256'],'scope':'historic direct guard and current point checks, inherited ancestry'},sort_keys=True))
