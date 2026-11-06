#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
d=Path(__file__).resolve().parents[2];p=d/'research/nine-seed38-jones-checkpoint27-34-check';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
for n,h in {'run.py':'983d5bf17bb7f2ec8e9a141e8a7d6a0d0271487701fc0a03c9909bb41a8c8292','provider_preflight.py':'b53613ed030fb3ae0f6cca75f1e4e388da841d285b3a0c15456d5cdf2bf579ed','source-manifest.json':'d7b13c2a052c408cefd9bc1ac0684fab56449940084685fd64ed89a9ffe86ea4','src/DiophantineConsistency/Norm38MacroCheckpoint27to34.lean':'4693daae8e6c0f64c75480e88fd3d240b1e6862b0af9461ce043a45757790ed0'}.items():assert sha(p/n)==h
s=(p/'src/DiophantineConsistency/Norm38MacroCheckpoint27to34.lean').read_text();rows=json.loads((p/'source-manifest.json').read_text())['rows'];assert len(rows)==1 and rows[0]['source_sha256']=='4693daae8e6c0f64c75480e88fd3d240b1e6862b0af9461ce043a45757790ed0';assert re.findall(r'^import ([\w.]+)$',s,re.M)==rows[0]['imports']==['DiophantineConsistency.Norm38MacroPath18to45','DiophantineConsistency.Norm38MacroLive18Group03','DiophantineConsistency.Norm38MacroPrefixInputsB'];assert re.findall(r'^theorem (\w+)',s,re.M)==['path27_34','lookup27_34','d34_phi_value']
path=s.split('theorem path27_34',1)[1].split('theorem lookup27_34',1)[0];assert 'PrefixPath d27 d34' in path and path.count('.castSucc')==7 and path.count('Dag.snoc')==7 and path.count('PrefixPath.step')==7
lookup=s.split('theorem lookup27_34',1)[1].split('theorem d34_phi_value',1)[0];assert '(i : Fin 27)' in lookup and lookup.count('.castSucc')==7 and 'lookup path27_34 a i' in lookup
phi=s.split('theorem d34_phi_value',1)[1].split('#print',1)[0];first=phi.split(':= by',1)[0];assert first.count('.castSucc')==19 and '= a ⟨5, by decide⟩' in first and 'lookup18_34 a ((Fin.last 14).castSucc.castSucc.castSucc)' in phi and 'd18_phi_carry a' in phi and 'prefix_phi a' in phi
nodes=(d/'research/nine-seed38-jones-named-prefix-check/src/DiophantineConsistency/Norm38MacroPrefixes.lean').read_text();assert 'def d15 : Dag 15 := .snoc d14 (.input ⟨5, by decide⟩)' in nodes
for j in range(28,35):assert f'def d{j} : Dag {j} := .snoc d{j-1} ' in nodes
r=subprocess.run([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],capture_output=True,text=True,check=True,timeout=300);o=json.loads(r.stdout);assert not r.stderr and o['status']=='PASS_NO_LEAN_PREFLIGHT' and o['stage_count']==1
print(json.dumps({'status':'PASS','preflight':o,'scope':'d27 to d34 path and concrete phi source; no Lean replay'},indent=2,sort_keys=True))
