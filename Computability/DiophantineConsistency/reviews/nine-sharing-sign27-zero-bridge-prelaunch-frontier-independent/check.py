#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];P=D/'research/nine-sharing-sign27-zero-bridge-check';H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
for n,h in {'run.py':'8b64a461f46253673b16e5e67d3e1df636bb2d37d33284201d638780c26a64fc','source-manifest.json':'3da864576e22b3a14185d6115a058ac772e075c4f71754e80f5e191655262e07','provider-union-survey.py':'cfd91d6d0a62ddceab8e1b5df33d00c22bdc32e1f1418201b52c544f4de2ae47','union.json':'d5b52134b0b081332ad62c789aa9d2b7b10e9cf88e98ad56962f2b5a11b3e2a1'}.items():assert H(P/n)==h
m=json.loads((P/'source-manifest.json').read_text())['rows'];assert [r['module'].split('.')[-1] for r in m]==['Sign27CoordinateDrop','Sign27ForwardBridge','Sign27ReverseBridge'];texts=[]
for e in m:
 n=e['module'].split('.')[-1];p=P/'src/DiophantineConsistency'/f'{n}.lean';assert H(p)==e['source_sha256']==H(D/f'research/nine-sharing-sign27-zero-bridge-draft/{n}.lean');texts.append(p.read_text())
c,f,b=texts;drop=c.split('def drop ',1)[1].split('![',1)[1].split(']',1)[0].split(', ');assert drop==[f'v {i}' for i in range(21)]+['u']+[f'v {i}' for i in range(23,29)]
for x in ['(hx : v 21 = u + 1) (hy : v 22 = u * (u + 2))','Sign27FirstCut.lift (drop u v) = v','drop (v 21) (Sign27FirstCut.lift v) = v']:assert x in c
for x in ['∃ u : V, v 21 = u + 1 ∧ v 22 = u * (u + 2) ∧','InternalZero (SharingSeed27Sextic.seed p) (drop u v)','Sign27SeedRootRecovery.recover p v hz','lift_drop v u hx hy']:assert x in b
ids=[1,2,3,4,5,9,10,11,12,13,14,16,17,18]
for s,prefix,count in [(f,'old',19),(b,'new',18)]:
 body=s.split('theorem '+prefix+'_rows ',1)[1].split(':= by rfl',1)[0];assert body.count('Sign27RemainingCuts.'+prefix+'R')==14 and body.count('Sign27AffectedCuts.'+prefix)==3 and body.count('Sign27FirstCut.oldN1')==(prefix=='old');assert s.count(' | rfl')==count-1
 for i in ids:assert f'Sign27RemainingCuts.R{i:02d}_eval' in s and f'Sign27RemainingCuts.{"new" if prefix=="old" else "old"}_R{i:02d}_row' in s
 for name in ['MainRoot','Dc2','NormalizedS']:assert f'Sign27AffectedCuts.{name}_eval' in s
 assert ('Sign27FirstCut.oldN1_zero' in s)==(prefix=='old')
for n,h in [('nine-sharing-sign27-remaining-cuts-terminal-frontier-independent','cc266749f6c4c4cb91534ef7cfbb6287af6a8a7c507b59251084d7cf2fee99ed'),('nine-sharing-sign27-affected-cuts-terminal-frontier-independent','b21ebe8973098c99d81abfa645d3468398fe99872948811da472b5a251fd20b3'),('nine-sharing-sign27-seed-root-recovery-terminal-frontier-independent','b810905848e81ee03d7e7fda162d1c454a05ae77ed5be77277b9b6bd44a8699c')]:
 p=D/'reviews'/n/'check.py';assert H(p)==h;subprocess.run([sys.executable,'-I','-S','-B',str(p)],capture_output=True,check=True,timeout=120)
r=subprocess.run([sys.executable,'-I','-S','-B',str(P/'run.py'),'--preflight'],capture_output=True,text=True,check=True,timeout=180);assert not r.stderr and json.loads(r.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_STATIC_AND_NO_LEAN_PREFLIGHT','scope':'proposed forward and existential reverse zero bridge with both coordinate reconstruction equations; no endpoint or Lean replay'},sort_keys=True,indent=2))
