#!/usr/bin/env python3
"""Source-only check of copied lift, 13 rows and exact list indices."""
import hashlib,json
from pathlib import Path
P=Path(__file__).resolve().parent;D=P.parents[1]
def rows(p):
 s=p.read_text().split('def remainingResiduals',1)[1].split('\n  ]',1)[0].split('\n  [\n',1)[1];return [x.strip().removesuffix(',') for x in s.splitlines()]
old=rows(D/'research/nine-sharing-sign31-sextic-lean-draft/SharingSeed31Sextic.lean');new=rows(D/'research/nine-sharing-sign28-sextic-lean-draft/SharingSeed28Sextic.lean');assert len(old)==21 and len(new)==18
spec=[('X',0,[('E',2,1),('mainRoot',6,5)],True),('c2',7,[('Dc2',8,6)],False),('normalizedS2',17,[('Na',19,16),('scaledNs',20,17)],False)]
for i,(n,oi,uses,hp) in enumerate(spec):
 s=(P/f'Sign28FirstCuts{i:02d}.lean').read_text();assert ('def old'+n+' (p : Fin 4 → ℤ) : Expr (Fin 32) :=\n  '+old[oi]+'\n') in s;assert f'(SharingSeed31Sextic.remainingResiduals p).drop {oi}' in s
 assert s.count('(hp0 : ((p 0 : ℤ) : DiffRing V) = ι beta)')==(1+len(uses) if hp else 0)
 for name,oj,nj in uses:
  assert ('def old'+name+' (p : Fin 4 → ℤ) : Expr (Fin 32) :=\n  '+old[oj]+'\n') in s
  assert ('def new'+name+' (p : Fin 4 → ℤ) : Expr (Fin 29) :=\n  '+new[nj]+'\n') in s
  assert f'(SharingSeed31Sextic.remainingResiduals p).drop {oj}' in s and f'(SharingSeed28Sextic.remainingResiduals p).drop {nj}' in s
orig=(D/'research/nine-sharing-sign28-sextic-lean-draft/SharingSeed28BridgeDraft.lean').read_text();s=(P/'Sign28FirstCuts00.lean').read_text();assert s.split('def lift ',1)[1].split('\n\n',1)[0]==orig.split('def lift ',1)[1].split('\n\n',1)[0]
out={'status':'pass','removed_rows':3,'affected_surviving_rows':5,'source_hashes':{p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted(P.glob('*.lean'))},'scope':'source text and row mapping only; no Lean checking or zero-set bridge'};(P/'result.json').write_text(json.dumps(out,indent=2,sort_keys=True)+'\n');print(json.dumps(out,sort_keys=True))
