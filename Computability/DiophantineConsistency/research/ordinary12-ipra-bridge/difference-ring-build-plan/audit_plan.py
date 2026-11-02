#!/usr/bin/env python3
"""Audit frozen source-declared union and tracked Git blobs; no compilation."""
import hashlib,json,re,subprocess
from pathlib import Path
if not __debug__:raise RuntimeError('guards require Python assertions enabled')
HERE=Path(__file__).resolve().parent;ROOT=HERE.parents[4]
H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
model=HERE/'model-closure-manifest.json';hist=Path('/tmp/ipra-aq29-fresh-source-closure-v2/manifest.json');rank=HERE.parent/'rank-adapter-prototype/replay-receipt.json'
for p,d in ((model,'859169fa08540764d0b02864fdeb7906301afcf4e1fea1e4b0e689c90df491b4'),(hist,'63b846158674d41beeaa99843d92008465f8e0fe5c45bb9e1fed4b78e1a2ab48'),(rank,'955f79233a43e2500aa2f477a51bc097ad419604b2306e908ff9fd54236d2a06')):
 if H(p)!=d:raise ValueError(('pin drift',str(p)))
a=json.loads(model.read_text());old=json.loads(hist.read_text())['sources'];rr=json.loads(rank.read_text());head=a['head'];names=set(a['sources'])|set(rr['source_closure'])
assert len(a['sources'])==19 and len(rr['source_closure'])==62 and len(names)==64
changed=[];new=[]
for n in sorted(names):
 row=a['sources'].get(n) or old[n];p=row['workspace_path'];raw=subprocess.check_output(['git','show',f'{head}:{p}'],cwd=ROOT)
 current=(ROOT/p).read_bytes()
 if raw!=current:raise ValueError(('workspace differs from frozen Git blob',n))
 digest=hashlib.sha256(raw).hexdigest()
 if n in a['sources'] and digest!=row['sha256']:raise ValueError(('model manifest drift',n))
 if n not in old:new.append(n)
 elif digest!=old[n]['sha256']:changed.append(n)
assert changed==['DiophantineConsistency.NaturalExpression']
assert new==['DiophantineConsistency.ModelDifferenceRing','DiophantineConsistency.WeightedExpressionDegree']
rankset=set(rr['source_closure']);reverse=set(changed)
while True:
 nextset=reverse|{n for n in rankset if any(d in reverse for d in old[n]['imports'])}
 if nextset==reverse:break
 reverse=nextset
assert len(reverse)==27
print('PASS_SOURCE_ONLY_MODEL_DIFFERENCE_PLAN 19 model 62 rank 64 union 2 new 1 drift 27 historical reverse')
print('HEAD',head)
print('NEW',', '.join(new))
print('DRIFT',', '.join(changed))
print('REVERSE',', '.join(sorted(reverse)))
