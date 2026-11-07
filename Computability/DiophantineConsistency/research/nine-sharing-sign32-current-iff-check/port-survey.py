#!/usr/bin/env python3
"""Bind the used current-data observation to successful rows of a failed producer."""
import hashlib,json,os
from pathlib import Path
P=Path(__file__).resolve().parent;D=P.parents[1];ROOT=Path('/tmp/nine-sharing-norm38-current-ports-split-20261105');BASE=Path('/tmp/nine-sharing-sign32-seed-iff-check-20261106');H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
def need(v,m):
 if not v:raise RuntimeError(m)
p=D/'research/nine-sharing-norm38-current-ports-split-draft/attempt01';need(H(p/'state.json')=='0f89b8b0a53abd15b0d7c1e20f198495775628e104fabc247c24efbd2cb81ad4' and H(p/'outer-terminal-author-record.json')=='05eed1d33296cb26c3f7d12c6a1de55d76c95a9df228741170f9bac1a285305a','receipt pin');d=json.loads((p/'state.json').read_text());need(d['status']=='FAILED' and len(d['rows'])>=2,'whole producer scope')
for i,name in enumerate(('Norm38CurrentPortBase','Norm38CurrentPort0')):
 r=d['rows'][i];need(r['module']==name and r['deps']['exit']==0 and r['compile']['exit']==0,'successful row '+name)
 need(H(ROOT/'src/DiophantineConsistency'/f'{name}.lean')==r['source_sha256'] and H(ROOT/'lib/DiophantineConsistency'/f'{name}.olean')==r['object_sha256'],'row bytes '+name)
 for k in ('deps','compile'):need(H(ROOT/f'{name}-{k}.txt')==r[k]['log_sha256'],'log '+name)
 for path,v in r['direct_guard'].items():
  q=Path(path)
  if v is None:need(not os.path.lexists(q),'unexpected '+path)
  else:need(q.is_file() and str(q.resolve())==v['realpath'] and H(q)==v['sha256'],'guard '+path)
r=d['rows'][0];obs=r['dependencies']['DiophantineConsistency.CurrentKernelData2011'];guard=r['direct_guard'].get(obs['path']);need(guard is not None and guard['sha256']==obs['sha256'] and guard['realpath']==obs['realpath'],'data guard observation')
q=BASE/'lib/DiophantineConsistency/CurrentKernelData2011.olean';need(q.is_file() and str(q.resolve())==obs['realpath'] and H(q)==obs['sha256'],'data overlay route')
original=D/'research/nine-sharing-norm38-current-ports-split-draft/src/DiophantineConsistency/Norm38CurrentPort0.lean';need(H(original)=='992697ca68fd43b53b07d36e6d374a16142e5d279144e9d7c84d25377a35b9c3','port0 source')
needle='rw [show CurrentWindowCarry2011.ports 0 = (CurrentMasks2011.beta : ℤ) from rfl,\n    Int.cast_natCast, map_natCast]'
need(needle in original.read_text() and needle in (P/'src/DiophantineConsistency/Sign32CurrentSeedIff.lean').read_text(),'port0 proof rewrite')
print(json.dumps({'status':'PASS','scope':'successful port-base/port0 rows within failed producer; current-data direct observation bound, deeper ancestry inherited','data_sha256':obs['sha256'],'data_realpath':obs['realpath']},sort_keys=True))
