#!/usr/bin/env python3
import hashlib,json,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];P=D/'research/nine-seed38-jones-vars-bd-retry01';Q=D/'research/nine-seed38-jones-vars-bd-check';sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
for n,h in {'run.py':'6cc34bb110d2d37800fc7bd128e2838fdeacee72c8058ac4edcbeafb7eab8e5d','provider_preflight.py':'a9c076c9051e1cf1d9179f64dc4d79438dd3c08b182f980fab695cb63b3a3f9e','source-manifest.json':'5bc125cc114aa0f6b52a937eec1a68445074ca8b37947197d85f005fe0dcbb7d','src/DiophantineConsistency/Norm38MacroVarsBd.lean':'013fdb21287af30502ab6d80f3690b8851ff8732215a6d5f580e6e9b941e982e'}.items():assert sha(P/n)==h
s=(Q/'src/DiophantineConsistency/Norm38MacroVarsBd.lean').read_text();t=(P/'src/DiophantineConsistency/Norm38MacroVarsBd.lean').read_text();old='  rfl\n\n#print axioms';new="  simp only [vars, RingVars.dvsr, RingVars.J, RingVars.F, RingVars.E, RingVars.D,\n    RingVars.C, RingVars.B', RingVars.W, RingVars.A, RingVars.M, RingVars.Y,\n    RingVars.U, Int.cast_ofNat, Nat.cast_ofNat]\n\n#print axioms";assert s.count(old)==1 and s.replace(old,new)==t
assert sha(Q/'attempt01/state.json')=='d02ac5f064202ad397b2951e0a99b5945493ee20f3e68d196dbefb126fe9b946'
R=D/'reviews/nine-seed38-jones-vars-bd-failure-frontier-independent';assert sha(R/'check.py')=='3a15541f25a28299c56741359c93f72f91a8c15eb85adbaeccb49fdb3e408ce2' and sha(R/'result.json')=='bcfdc11e1e0307233ab8f9f5791046d693edec46364a9505e8db1c52457ba477'
r=subprocess.run([sys.executable,'-I','-S','-B',str(P/'run.py'),'--preflight'],capture_output=True,text=True,timeout=120,check=True);assert not r.stderr;x=json.loads(r.stdout);assert x['status']=='PASS_NO_LEAN_PREFLIGHT' and x['stage_count']==1
print(json.dumps({'status':'PASS_NO_LEAN','preflight':x,'scope':'unchanged Bd cut statement, explicit RingVars/cast simplification proof retry; no Lean or full named semantics'},indent=2,sort_keys=True))
