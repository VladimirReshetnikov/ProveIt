#!/usr/bin/env python3
import hashlib,json
from pathlib import Path
D=Path(__file__).resolve().parents[2]
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def need(x,m):
 if not x:raise RuntimeError(m)
state=D/'research/nine-sharing-sign33-windows-retry01/attempt01/state.json'
checker=D/'reviews/nine-sharing-sign33-windows-retry01-terminal-frontier-independent/check.py'
need(sha(state)=='9bba240fcea1e0efc75c9c8022016c61b68a0dfeabb05d66ea4b28786899faa1','windows state drift');need(sha(checker)=='cb43319a1c4a99071d55f00ba03db680b2d206ec59c922410cb2fc1909d17e27','windows audit checker drift')
s=json.loads(state.read_text());need(s['status']=='PASS' and len(s['rows'])==1,'windows state')
r=s['rows'][0];need(r['module']=='Sign33Windows' and r['deps']['exit']==0 and r['compile']['exit']==0,'windows stage')
d=r['dependencies']['DiophantineConsistency.ArithmeticPellFirstIndex'];need(r['direct_guard'][d['path']]=={'realpath':d['realpath'],'sha256':d['sha256']},'historic direct guard')
need(d['sha256']=='20d3769d891a42810c1985203768b122bf936884494d2829415e3140d6deb9c2','historic object hash')
for p in [Path(d['path']),Path('/tmp/nine-sharing-sign14-transport-row-check-20261110/lib/DiophantineConsistency/ArithmeticPellFirstIndex.olean')]:
 need(p.is_file() and str(p.resolve())==d['realpath'] and sha(p)==d['sha256'],'current provider drift')
print(json.dumps({'status':'PASS','realpath':d['realpath'],'sha256':d['sha256'],'scope':'historic direct guard and current point checks, inherited ancestry'},sort_keys=True))
