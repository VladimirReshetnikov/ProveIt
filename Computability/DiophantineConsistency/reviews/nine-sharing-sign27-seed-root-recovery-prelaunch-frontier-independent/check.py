#!/usr/bin/env python3
import hashlib,json,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];P=D/'research/nine-sharing-sign27-seed-root-recovery-check';H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
for n,h in {'run.py':'9842a39912fe33b6b31d2a035a66669256aa83b5d9cd1764f3391103873062fd','source-manifest.json':'d677e1bb319fe093e17300fe05f8641139581179a31efb35a1d4b87578505892','src/DiophantineConsistency/Sign27SeedRootRecovery.lean':'98b80aa4e79174424b44c90d7b753280f269b47614b314782956471b8e8e80a1'}.items():assert H(P/n)==h
m=json.loads((P/'source-manifest.json').read_text())['rows'];assert len(m)==1 and m[0]['imports']==['DiophantineConsistency.Sign27RootRecovery'];s=(P/'src/DiophantineConsistency/Sign27SeedRootRecovery.lean').read_text()
for x in ['(Expr.var 21 * Expr.var 21 - Expr.var 22) - Expr.constant (1 : ℤ)','SharingSign28Squares.seed_zero_iff_residuals p v','oldN1_row p','(sub_eq_iff_eq_add).mp (sub_eq_zero.mp he)','Sign27RootRecovery.recover (v 21) (v 22) hnorm','∃ u : V, v 21 = u + 1 ∧ v 22 = u * (u + 2)']:assert x in s
provider=D/'research/nine-sharing-sign28-sextic-lean-draft/SharingSeed28Sextic.lean';assert '((((Expr.var 21) * (Expr.var 21)) - (Expr.var 22)) - (Expr.constant (1 : ℤ)))' in provider.read_text()
f=D/'reviews/nine-sharing-sign27-root-recovery-terminal-frontier-independent/check.py';assert H(f)=='96ee0f9f5686ce2bd3aaf15395d13cd1e344d892ce554cb0b7164c57cfe9c6f7';subprocess.run([sys.executable,'-I','-S','-B',str(f)],check=True,capture_output=True,timeout=60)
r=subprocess.run([sys.executable,'-I','-S','-B',str(P/'run.py'),'--preflight'],capture_output=True,text=True,check=True,timeout=120);assert not r.stderr and json.loads(r.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_STATIC_AND_NO_LEAN_PREFLIGHT','scope':'proposed predecessor and second-coordinate extraction from sign28 seed zero only'},sort_keys=True,indent=2))
