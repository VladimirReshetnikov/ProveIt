#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];P=D/'research/nine-sharing-sign32-current-iff-check';sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
for n,h in {'run.py':'59d06591e2fef25b9fe54e4dc922fec506b71a54a2b0c5112b27927ffb6093e5','port-survey.py':'7f64024c2f0100e9ed58a8fb2e538013bcc9414031745691b6adb615cfad50a8','source-manifest.json':'635e18499bf687c3dcac4e5711984b39a55bcb25a219e25b8ac692f0ccc1035c','src/DiophantineConsistency/Sign32CurrentSeedIff.lean':'539a3ee54ae3c05ac7572a1181214100c5a7cb61bf548ff1c4557871493e30f5'}.items():assert sha(P/n)==h
r=json.loads((P/'source-manifest.json').read_text())['rows'];assert len(r)==1 and r[0]['imports']==['DiophantineConsistency.Sign32SeedExistential','DiophantineConsistency.CurrentKernelData2011']
s=(P/'src/DiophantineConsistency/Sign32CurrentSeedIff.lean').read_text();assert re.findall(r'^theorem (\w+)',s,re.M)==['port0','pointwise','exists_same_input'] and len(re.findall(r'^#print axioms ',s,re.M))==3
assert '[ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]' in s
assert '((CurrentWindowCarry2011.ports 0 : ℤ) : DiffRing V) = ι (CurrentMasks2011.beta : V)' in s and 'Int.cast_natCast, map_natCast]' in s
assert 'Sign32SeedIff.pointwise CurrentWindowCarry2011.ports (CurrentMasks2011.beta : V) v port0' in s and 'Sign32SeedIff.exists_same_input CurrentWindowCarry2011.ports (CurrentMasks2011.beta : V) x port0' in s
assert '(∃ v : Fin 33 → V, v 0 = x ∧ InternalZero (SharingSeed32Sextic.seed CurrentWindowCarry2011.ports) v) ↔' in s and '(∃ v : Fin 34 → V, v 0 = x ∧ InternalZero (SharingSeed33.seed CurrentWindowCarry2011.ports) v)' in s
assert 'def ports (K : ℤ) : Fin 4 → ℤ := ![beta, K, lowPort, highPort + beta]' in (D/'Lean/DiophantineConsistency/CurrentMaskData2011.lean').read_text()
pre=subprocess.run([sys.executable,'-I','-S','-B',str(P/'run.py'),'--preflight'],capture_output=True,text=True,timeout=120,check=True);assert not pre.stderr;x=json.loads(pre.stdout);assert x['status']=='PASS_NO_LEAN_PREFLIGHT' and x['stage_count']==1
print(json.dumps({'status':'PASS_NO_LEAN','preflight':x,'scope':'current Lean ports, local beta cast, pointwise and same-input seed iff; no JSON byte binding or sextic Jones endpoint'},indent=2,sort_keys=True))
