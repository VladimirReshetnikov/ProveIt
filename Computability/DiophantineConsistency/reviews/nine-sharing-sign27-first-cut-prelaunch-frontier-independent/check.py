#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];P=D/'research/nine-sharing-sign27-first-cut-check';H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
for n,h in {'run.py':'8868b9de3d9791eb0ebc4b4306b6faf7b27688f2cb885aa5c6effd0529caf945','source-manifest.json':'7e825824be0ff6b0d2dfee607a682a57a0dd93e5480e393817d2a054d3fc42ab','sign28-survey.py':'eda25e29ad5397a980627ebfc04687b5b2b07a0adb7ce5ef3788b5e4ae0bfeff','src/DiophantineConsistency/Sign27FirstCut.lean':'6219d8aa463618455ada24b85a10ee269cee1593ca3668872768581182f63719'}.items():assert H(P/n)==h
m=json.loads((P/'source-manifest.json').read_text())['rows'];assert len(m)==1 and m[0]['imports']==['DiophantineConsistency.SharingSign27Squares','DiophantineConsistency.SharingSign28Squares'];s=(P/'src/DiophantineConsistency/Sign27FirstCut.lean').read_text()
draft=(D/'research/nine-sharing-sign27-sextic-lean-draft/SharingSeed27BridgeDraft.lean').read_text();assert s.split('def lift ',1)[1].split('\n\n',1)[0]==draft.split('def lift ',1)[1].split('\n\n',1)[0]
for x in ['(Expr.var 21 * Expr.var 21 - Expr.var 22) - Expr.constant (1 : ℤ)','theorem oldN1_row','theorem oldN1_zero','theorem first_eval','SharingSeed28Sextic.firstResidual p','SharingSeed27Sextic.firstResidual p','𝗜𝚺₁']:assert x in s
lines=[]
for n in (27,28):
 f=D/f'research/nine-sharing-sign{n}-sextic-lean-draft'/f'SharingSeed{n}Sextic.lean';t=f.read_text();lines.append(t.split('def firstResidual ',1)[1].split(':=\n',1)[1].split('\n',1)[0])
assert lines[0]==lines[1]
r=subprocess.run([sys.executable,'-I','-S','-B',str(P/'run.py'),'--preflight'],capture_output=True,text=True,check=True,timeout=120);assert not r.stderr and json.loads(r.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_STATIC_AND_NO_LEAN_PREFLIGHT','scope':'lift, deleted N1 row/zero, first common residual identity only'},sort_keys=True,indent=2))
