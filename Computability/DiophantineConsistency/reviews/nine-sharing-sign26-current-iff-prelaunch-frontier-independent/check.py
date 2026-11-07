#!/usr/bin/env python3
import hashlib,json,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];P=D/'research/nine-sharing-sign26-current-iff-check';R=D.parents[1]
H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
pins={'run.py':'527e1e80355e02e56c6a29cb5d3951223632d8c836125f8a8f1ecaa6fc52d615','source-manifest.json':'b054d17ea884ed6be9cd10f2062c429929540267e4699b60daa3276d479e6531','provider-survey.py':'9dd36c79ca02c2260db91c23421e3de2829fe17836715717308c6ec963f6abb7','src/DiophantineConsistency/Sign26CurrentSeedIff.lean':'a8e8b842f1b209411166560e73a3be695a8821e7d3a8037dc1a282cb5e7ca482'}
for p,h in pins.items():assert H(P/p)==h
m=json.loads((P/'source-manifest.json').read_text());assert len(m['rows'])==1;e=m['rows'][0];assert e['module']=='DiophantineConsistency.Sign26CurrentSeedIff' and e['imports']==['DiophantineConsistency.Sign26SeedExistential','DiophantineConsistency.Sign26CurrentHypotheses'] and e['source_sha256']==pins['src/DiophantineConsistency/Sign26CurrentSeedIff.lean'];assert H(R/e['source'])==e['source_sha256']
source=(P/'src/DiophantineConsistency/Sign26CurrentSeedIff.lean').read_text();assert 'Sign26SeedIff.exists_same_input CurrentWindowCarry2011.ports' in source and all(x in source for x in ('Sign26CurrentHypotheses.port0','Sign26CurrentHypotheses.port1','Sign26CurrentHypotheses.beta_ge_one','∃ v : Fin 27 → V','∃ v : Fin 28 → V','v 0 = x'))
for p,h in [('reviews/nine-sharing-sign26-seed-iff-terminal-frontier-independent/check.py','b78b92433be6cbc79eab65ffe3639b6c638289cec21aa40c86ca13bdd924e7f5'),('reviews/nine-sharing-sign26-current-hypotheses-terminal-frontier-independent/check.py','4f4eb9907e1139cc3fc03f358d0972667f32735fa687bbe8ae8e44eebae115bc')]:
 q=D/p;assert H(q)==h;subprocess.run([sys.executable,'-I','-S','-B',str(q)],check=True,capture_output=True,timeout=120)
r=subprocess.run([sys.executable,'-I','-S','-B',str(P/'provider-survey.py')],check=True,capture_output=True,text=True,timeout=120);s=json.loads(r.stdout);assert s['status']=='PASS' and s['common_count']==1063 and s['extra_count']==0 and s['object_sha256']=='c4692189c4b27b48777b545bfa7829f01a06916d3d7c43a4de09602752efb88c'
r=subprocess.run([sys.executable,'-I','-S','-B',str(P/'run.py'),'--preflight'],check=True,capture_output=True,text=True,timeout=120);assert json.loads(r.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_PRELAUNCH','scope':'current-port same-input existential sign26/sign27 seed iff over IΣ₁; no source or iPRA endpoint','overlapping_links':1063,'independent_no_lean_preflight':'PASS'},indent=2,sort_keys=True))
