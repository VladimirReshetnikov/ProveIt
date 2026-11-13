#!/usr/bin/env python3
import hashlib,json,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];P=D/'research/nine-sharing-sign26-current-seed-gap-check';H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
for n,h in {'run.py':'912121dafc442885673dabceb2997d2225c7064bf0537d8cd4ba03f567c1a243','source-manifest.json':'2e5da5faf77d4be3333142dc8a4f78ee7791cfcfa5dd11ff2cfb091deaa98993','src/DiophantineConsistency/Sign26CurrentSeedGap.lean':'5ce4dc1f7c68393e7c4faa6156294c8809568bc82a1bc5c13da98cc37ddd2545'}.items():assert H(P/n)==h
m=json.loads((P/'source-manifest.json').read_text())['rows'];assert len(m)==1 and m[0]['imports']==['DiophantineConsistency.Sign26CurrentHypotheses'];s=(P/'src/DiophantineConsistency/Sign26CurrentSeedGap.lean').read_text();assert H(D/'research/nine-sharing-sign26-current-seed-gap-draft/Sign26CurrentSeedGap.lean')==m[0]['source_sha256']
for x in ['[V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]','(hz : InternalZero (SharingSeed26Sextic.seed CurrentWindowCarry2011.ports) v)','∃ gap : V, ι gap =','Sign26SeedGap.exists_gap CurrentWindowCarry2011.ports (CurrentMasks2011.beta : V)','(CurrentKernel2011.K : V) v Sign26CurrentHypotheses.port0 Sign26CurrentHypotheses.port1','Sign26CurrentHypotheses.beta_ge_one hz']:assert x in s
up=D/'reviews/nine-sharing-sign26-current-hypotheses-terminal-frontier-independent/check.py';assert H(up)=='4f4eb9907e1139cc3fc03f358d0972667f32735fa687bbe8ae8e44eebae115bc';subprocess.run([sys.executable,'-I','-S','-B',str(up)],capture_output=True,check=True,timeout=120)
r=subprocess.run([sys.executable,'-I','-S','-B',str(P/'run.py'),'--preflight'],capture_output=True,text=True,check=True,timeout=180);assert not r.stderr and json.loads(r.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_STATIC_AND_NO_LEAN_PREFLIGHT','scope':'current-port seed zero implies represented gap under IΣ₁; no q3 transfer or Lean replay'},sort_keys=True,indent=2))
