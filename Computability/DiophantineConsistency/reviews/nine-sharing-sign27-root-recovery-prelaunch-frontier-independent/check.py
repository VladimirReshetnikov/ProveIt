#!/usr/bin/env python3
import hashlib,json,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];P=D/'research/nine-sharing-sign27-root-recovery-check';H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
for n,h in {'run.py':'4dd29b718953a2986978b008adaf78c9c18c1037b9947d163e828222e3e311dd','source-manifest.json':'c153067c6d60439ca1d1152ea7d1eb8c8c1d4c647ca79a97cd04971022e13832','src/DiophantineConsistency/Sign27RootRecovery.lean':'c3c6a7911ceac78ae41be6abf003707e1e613158cb48d95d268c466357939e33'}.items():assert H(P/n)==h
m=json.loads((P/'source-manifest.json').read_text())['rows'];assert len(m)==1 and m[0]['imports']==['DiophantineConsistency.SharingSign28Squares'];s=(P/'src/DiophantineConsistency/Sign27RootRecovery.lean').read_text()
for x in ['(x y : V) (h : ι x * ι x = ι y + 1)','∃ u : V, x = u + 1 ∧ y = u * (u + 2)','zero_or_succ x','ι_nonneg y','zero_lt_one','rw [huR, hid] at h','(add_right_cancel h).symm','ι_injective','map_ofNat','𝗜𝚺₁']:assert x in s
r=subprocess.run([sys.executable,'-I','-S','-B',str(P/'run.py'),'--preflight'],capture_output=True,text=True,check=True,timeout=120);assert not r.stderr and json.loads(r.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_STATIC_AND_NO_LEAN_PREFLIGHT','scope':'abstract root recovery from explicit embedded ring equality only'},sort_keys=True,indent=2))
