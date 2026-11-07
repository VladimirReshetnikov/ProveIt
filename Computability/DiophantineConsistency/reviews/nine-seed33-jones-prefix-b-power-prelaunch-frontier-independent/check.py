#!/usr/bin/env python3
import hashlib,json,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];P=D/'research/nine-seed33-jones-prefix-b-power-check';H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
for n,h in {'run.py':'e5e4ccd0a1db7b188596f9148d4fc13ff2b44950a45d6b05f9aa802647236107','source-manifest.json':'5d94b5dea3afab51deb2800b72e00e554f533585e6c7910742796e1b23c58da7','src/DiophantineConsistency/Sign33MacroPrefixBPower.lean':'4f538e876c44524549712703696ea54c6e810cf772c7f7b34e3cf66be3dabbda'}.items():assert H(P/n)==h
m=json.loads((P/'source-manifest.json').read_text())['rows'];assert len(m)==1 and m[0]['imports']==['DiophantineConsistency.Sign33MacroPrefixCarryOthers']
f=P/'src/DiophantineConsistency/Sign33MacroPrefixBPower.lean';s=f.read_text();old=D/'research/nine-seed38-jones-prefix-b-power-check/src/DiophantineConsistency/Norm38MacroPrefixBPower.lean';assert s==old.read_text().replace('Norm38','Sign33') and H(f)==m[0]['source_sha256']
assert '((Fin.last 1)'+'.castSucc'*8+')' in s and '((Fin.last 0)'+'.castSucc'*9+')' in s and 'rw [d10_B_carry, d10_b_carry, d9_B, d9_b]' in s and '^ (5 : Nat)' in s
r=subprocess.run([sys.executable,'-I','-S','-B',str(P/'run.py'),'--preflight'],capture_output=True,text=True,check=True,timeout=120);assert not r.stderr and json.loads(r.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_STATIC_AND_NO_LEAN_PREFLIGHT','scope':'proposed d10 B=b^5 short-prefix relation only'},sort_keys=True,indent=2))
