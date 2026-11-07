#!/usr/bin/env python3
"""Source-only audit of the 19 unaffected reindexing rows and first q³ row."""
import json,re
from pathlib import Path
P=Path(__file__).resolve().parent;D=P.parents[1]
def rows(p):
 s=p.read_text().split('def remainingResiduals',1)[1].split('\n  ]',1)[0].split('\n  [\n',1)[1];return [x.strip().removesuffix(',') for x in s.splitlines()]
oldpath=D/'research/nine-sharing-sign32-sextic-lean-draft/SharingSeed32Sextic.lean';newpath=D/'research/nine-sharing-sign31-sextic-lean-draft/SharingSeed31Sextic.lean';old=rows(oldpath);new=rows(newpath);neednames=[('X',0,0),('Y',1,1),('E',2,2),('kY',3,3),('ell',4,4),('Delta',5,5),('mainRoot',6,6),('c2',7,7),('Dc2',8,8),('N1',9,9),('gap',10,10),('tau',11,11),('N0',12,12),('Nt',13,13),('cTminusR',15,14),('normalizedS',17,16),('normalizedS2',18,17),('V2minusY2',19,18),('Na',20,19)];assert len(old)==22 and len(new)==21
for i,(n,oi,ni) in enumerate(neednames):
 s=(P/'src/DiophantineConsistency'/f'Sign31RemainingCuts{0 if i<9 else 1:02d}.lean').read_text()
 assert ('def old'+n+' (p : Fin 4 → ℤ) : Expr (Fin 33) :=\n  '+old[oi]+'\n') in s
 assert ('def new'+n+' (p : Fin 4 → ℤ) : Expr (Fin 32) :=\n  '+new[ni]+'\n') in s
 assert f'(SharingSeed32Sextic.remainingResiduals p).drop {oi}' in s and f'(SharingSeed31Sextic.remainingResiduals p).drop {ni}' in s
 assert re.search(r'Expr\.var 27\b',old[oi]) is None
oldfirst=oldpath.read_text().split('def firstResidual',1)[1].split('\n',2)[1];assert re.search(r'Expr\.var 27\b',oldfirst) is None
s=(P/'src/DiophantineConsistency/Sign31RemainingCuts00.lean').read_text();assert '(SharingSeed32Sextic.firstResidual p)' in s and '(SharingSeed31Sextic.firstResidual p)' in s
print(json.dumps({'status':'PASS','unaffected_remaining_rows':19,'first_residual':'q3','scope':'source text checks only; no Lean or zero-set bridge'},sort_keys=True))
