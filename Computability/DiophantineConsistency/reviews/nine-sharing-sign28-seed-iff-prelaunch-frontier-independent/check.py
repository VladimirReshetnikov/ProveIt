#!/usr/bin/env python3
import hashlib,json,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];P=D/'research/nine-sharing-sign28-seed-iff-check';H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
for n,h in {'run.py':'6bd046249d5c548494561f9fe9bd8ebf8ccd7ec521b8ebb3536fdd2c1de129c8','source-manifest.json':'961181a000cec1b9fba3b5e430c3a45808b578182acd6b1b67a38f18227f6490','first-cuts-survey.py':'ba7bf651c766d5adc57e8fd5e7d3c55ac7d9cc43335a212ac1bff1fad774285e'}.items():assert H(P/n)==h
m=json.loads((P/'source-manifest.json').read_text())['rows'];assert [r['module'] for r in m]==['DiophantineConsistency.Sign28SeedPointwise','DiophantineConsistency.Sign28SeedExistential'];src=[]
for row in m:
 f=P/'src/DiophantineConsistency'/(row['module'].split('.')[-1]+'.lean');s=f.read_text();assert H(f)==row['source_sha256'] and [x[7:] for x in s.splitlines() if x.startswith('import ')]==row['imports'];src.append(s)
a,b=src
for s in src:assert '(hp0 : ((p 0 : ℤ) : DiffRing V) = ι beta)' in s and '𝗜𝚺₁' in s
assert 'Sign28CoordinateRecover.drop (Sign28FirstCuts.lift beta v) = v' in a and 'Sign28ZeroBridge.forward p beta v hp0' in a and 'Sign28ZeroBridge.backward p beta (Sign28FirstCuts.lift beta v) hp0 hz' in a and 'simpa only [drop_lift]' in a
assert '(∃ v : Fin 29 → V, v 0 = x ∧ InternalZero (SharingSeed28Sextic.seed p) v)' in b and '(∃ v : Fin 32 → V, v 0 = x ∧ InternalZero (SharingSeed31Sextic.seed p) v)' in b and 'Sign28ZeroBridge.forward p beta v hp0 hz' in b and 'Sign28ZeroBridge.backward p beta v hp0 hz' in b
q=D/'reviews/nine-sharing-sign28-zero-bridge-terminal-frontier-independent/check.py';assert H(q)=='5e05f8aee82844d520d04905f9f27ee72bc9a66dd5b6bb0637b57e2d30a8c17d';subprocess.run([sys.executable,'-I','-S','-B',str(q)],check=True,capture_output=True,timeout=30)
r=subprocess.run([sys.executable,'-I','-S','-B',str(P/'run.py'),'--preflight'],capture_output=True,text=True,check=True,timeout=120);assert not r.stderr and json.loads(r.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_STATIC_AND_NO_LEAN_PREFLIGHT','stages':2,'scope':'proposed pointwise and same-input existential equivalence with beta cast in IΣ₁; no endpoint claim'},sort_keys=True,indent=2))
