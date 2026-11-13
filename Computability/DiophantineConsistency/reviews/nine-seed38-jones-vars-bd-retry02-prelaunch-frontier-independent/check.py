#!/usr/bin/env python3
import hashlib,json,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];P=D/'research/nine-seed38-jones-vars-bd-retry02';Q=D/'research/nine-seed38-jones-vars-bd-retry01';sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
for n,h in {'run.py':'3e1db39d2b54552fc0efacb5b8139a04cac665ecb03d9a7f1b96b992e1c36012','provider_preflight.py':'44068d261a8001f718bcdee7a479479b0067e3ef0f4c9a222924da0bbea27cc9','source-manifest.json':'5f3b3188abdc8299222db784e99a5810b5b5ed1b6ca80c941d35524d6439f029','src/DiophantineConsistency/Norm38MacroVarsBd.lean':'099442f1db440cfb6a023d8ee11d5f8a253f5c02a51d1946d4af7731486d2bb4'}.items():assert sha(P/n)==h
s=(Q/'src/DiophantineConsistency/Norm38MacroVarsBd.lean').read_text();t=(P/'src/DiophantineConsistency/Norm38MacroVarsBd.lean').read_text();old='Int.cast_ofNat, Nat.cast_ofNat]';new='Int.cast_ofNat, Int.cast_one]';assert s.count(old)==1 and s.replace(old,new)==t
assert sha(Q/'attempt01/state.json')=='24a922a65cafe434716404a587e5539965014ea5c2d6f32074f1b7c80daa6d28'
R=D/'reviews/nine-seed38-jones-vars-bd-retry01-failure-frontier-independent';assert sha(R/'check.py')=='c65f9f471a666b24a45da909b088073e0303afcc0d0620bc0e29f15ebe74f14a' and sha(R/'result.json')=='3c9de3fb15121eaba3784c0367f75b311b33db3bb079801afa2e7bbfe314fc8c'
r=subprocess.run([sys.executable,'-I','-S','-B',str(P/'run.py'),'--preflight'],capture_output=True,text=True,timeout=120,check=True);assert not r.stderr;x=json.loads(r.stdout);assert x['status']=='PASS_NO_LEAN_PREFLIGHT' and x['stage_count']==1
print(json.dumps({'status':'PASS_NO_LEAN','preflight':x,'scope':'unchanged Bd cut statement, explicit Int.cast_one proof retry; no Lean or full named semantics'},indent=2,sort_keys=True))
