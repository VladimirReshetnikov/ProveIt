#!/usr/bin/env python3
import hashlib,json,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];P=D/'research/nine-seed33-jones-rankcode-link-check';H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
for n,h in {'run.py':'8494b29c8272e982c8d0cd37d8316d4261f7fd4543bc292f754dcffd606a6699','source-manifest.json':'c4fcdb0a172e3447519c5441083bb04a67c1ff296c131447ed49fb244a8a3535','src/DiophantineConsistency/Sign33MacroRankCodeLink.lean':'d9b98f17305f13a843bf532c14f6b95c20b1ae2706d8f36de4558921e8ef38a0'}.items():assert H(P/n)==h
m=json.loads((P/'source-manifest.json').read_text())['rows'];assert len(m)==1 and m[0]['imports']==['DiophantineConsistency.Sign33MacroRankCarry'];f=P/'src/DiophantineConsistency/Sign33MacroRankCodeLink.lean';s=f.read_text();old=D/'research/nine-seed38-jones-rankcode-link-check/src/DiophantineConsistency/Norm38MacroRankCodeLink.lean';assert s==old.read_text().replace('Norm38','Sign33') and H(f)==m[0]['source_sha256'];assert 'rankRaw z b (b ^ (5 : Nat)) q n e ell lam g theta' in s and 'NinePolynomial.rankCode (1 : R) z b e g ell n q theta lam' in s
r=subprocess.run([sys.executable,'-I','-S','-B',str(P/'run.py'),'--preflight'],capture_output=True,text=True,check=True,timeout=120);assert not r.stderr and json.loads(r.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_STATIC_AND_NO_LEAN_PREFLIGHT','scope':'generic commutative-ring rankRaw/rankCode identity only'},sort_keys=True,indent=2))
