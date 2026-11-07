#!/usr/bin/env python3
"""Source-only check of 13 unaffected rows and first q³ row."""
import hashlib,json,re
from pathlib import Path
P=Path(__file__).resolve().parent;D=P.parents[1];Q=P/'src/DiophantineConsistency'
def rows(p):
 s=p.read_text().split('def remainingResiduals',1)[1].split('\n  ]',1)[0].split('\n  [\n',1)[1];return [x.strip().removesuffix(',') for x in s.splitlines()]
oldpath=D/'research/nine-sharing-sign31-sextic-lean-draft/SharingSeed31Sextic.lean';newpath=D/'research/nine-sharing-sign28-sextic-lean-draft/SharingSeed28Sextic.lean';old=rows(oldpath);new=rows(newpath);entries=[('Y',1,0),('kY',3,2),('ell',4,3),('Delta',5,4),('N1',9,7),('gap',10,8),('tau',11,9),('N0',12,10),('Nt',13,11),('cTminusR',14,12),('V',15,13),('normalizedS',16,14),('V2minusY2',18,15)];assert len(old)==21 and len(new)==18
for i,(n,oi,ni) in enumerate(entries):
 s=(Q/f'Sign28RemainingCuts{0 if i<6 else 1:02d}.lean').read_text()
 assert ('def old'+n+' (p : Fin 4 → ℤ) : Expr (Fin 32) :=\n  '+old[oi]+'\n') in s
 assert ('def new'+n+' (p : Fin 4 → ℤ) : Expr (Fin 29) :=\n  '+new[ni]+'\n') in s
 assert f'(SharingSeed31Sextic.remainingResiduals p).drop {oi}' in s and f'(SharingSeed28Sextic.remainingResiduals p).drop {ni}' in s
 assert not re.search(r'Expr\.var (?:16|23|30)\b',old[oi])
oldfirst=oldpath.read_text().split('def firstResidual',1)[1].split('\n',2)[1];assert not re.search(r'Expr\.var (?:16|23|30)\b',oldfirst)
s=(Q/'Sign28RemainingCuts00.lean').read_text();assert '(SharingSeed31Sextic.firstResidual p)' in s and '(SharingSeed28Sextic.firstResidual p)' in s
out={'status':'PASS','unaffected_remaining_rows':13,'first_residual':'q3','source_hashes':{p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted(Q.glob('*.lean'))},'scope':'source text only; no Lean or zero-set bridge'};print(json.dumps(out,sort_keys=True))
