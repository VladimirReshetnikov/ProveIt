#!/usr/bin/env python3
import hashlib,json
from pathlib import Path
D=Path(__file__).resolve().parents[2];P=D/'research/nine-sharing-sign28-seed-squares-check';sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert sha(P/'run.py')=='6f1569c9926f8a76a428c2d007ee06515b10bbcd01d95e7eaebc050ceaa966fe' and sha(P/'source-manifest.json')=='ee3ad478023e57b92ef5197ea961e26a6f365d1b85293b158c50a589970d2c4f'
m=json.loads((P/'source-manifest.json').read_text())['rows'];names=['SharingSeed28Sextic','SharingSign28Squares'];assert [r['module'].split('.')[-1] for r in m]==names
for row,n in zip(m,names):
 p=P/'src/DiophantineConsistency'/f'{n}.lean';s=p.read_text();assert sha(p)==row['source_sha256'] and [x[7:] for x in s.splitlines() if x.startswith('import ')]==row['imports']
assert sha(P/'src/DiophantineConsistency/SharingSeed28Sextic.lean')=='ccc091d8b88f3f165c86fd8308c7ba35217979aa21a6412437a6fb1015394800'
s=(P/'src/DiophantineConsistency/SharingSign28Squares.lean').read_text()
for x in ('(p : Fin 4 → ℤ) (v : Fin 29 → V)','InternalZero (SharingSeed28Sextic.seed p) v ↔','SharingSeed28Sextic.firstResidual p :: SharingSeed28Sextic.remainingResiduals p','SharingSign33Squares.squareSum_zero_iff','InternalZero e v'):assert x in s
assert s.count('#print axioms')==1
print(json.dumps({'status':'PASS_STATIC','scope':'symbolic-port Fin29 same-valuation square-sum decomposition only; no sign31 bridge'}))
