#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
d=Path(__file__).resolve().parents[2];p=d/'research/nine-seed38-jones-checkpoint41-45-check';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
for n,h in {'run.py':'4fbf346e1ad173a7c25bf3c8c6d7568c4e60406e612c8d96453568c800c708a8','provider_preflight.py':'7d933724ac9ce67b0a700d8e36c09895ee6400cd3341cc959ad1a5ba95bab8ed','source-manifest.json':'31a0b33f58406fdacfa54812fa8a32f2c0f4de1011e669777b4dff9b01f84f1e','src/DiophantineConsistency/Norm38MacroCheckpoint41to45.lean':'606c7c153863e98662eadb430b442cc28bebec34e4676446b2066c5b6eedf249'}.items():assert sha(p/n)==h
s=(p/'src/DiophantineConsistency/Norm38MacroCheckpoint41to45.lean').read_text();rows=json.loads((p/'source-manifest.json').read_text())['rows'];assert len(rows)==1 and rows[0]['source_sha256']=='606c7c153863e98662eadb430b442cc28bebec34e4676446b2066c5b6eedf249';assert re.findall(r'^import ([\w.]+)$',s,re.M)==rows[0]['imports']==['DiophantineConsistency.Norm38MacroCheckpoint34to41','DiophantineConsistency.Norm38MacroLive18Group01','DiophantineConsistency.Norm38MacroLive18Group02','DiophantineConsistency.Norm38MacroPrefixGsmall','DiophantineConsistency.Norm38MacroPrefixGlarge'];assert re.findall(r'^theorem (\w+)',s,re.M)==['path41_45','lookup41_45','lookup_recipe41','d41_g_value','d41_G_value']
path=s.split('theorem path41_45',1)[1].split('theorem lookup41_45',1)[0];assert 'PrefixPath d41 d45' in path and path.count('.castSucc')==4 and path.count('Dag.snoc')==4 and path.count('PrefixPath.step')==4
lookup=s.split('theorem lookup41_45',1)[1].split('theorem lookup_recipe41',1)[0];assert '(i : Fin 41)' in lookup and lookup.count('.castSucc')==4 and 'lookup path41_45 a i' in lookup
recipe=s.split('theorem lookup_recipe41',1)[1].split('theorem d41_g_value',1)[0];assert 'Norm38MacroRecipe.recipe.values a' in recipe and recipe.count('.castSucc')==4 and 'rw [recipe_eq_named]' in recipe
g=s.split('theorem d41_g_value',1)[1].split('theorem d41_G_value',1)[0];G=s.split('theorem d41_G_value',1)[1].split('#print',1)[0];assert g.split(':= by',1)[0].count('.castSucc')==33 and 'a ⟨1, by decide⟩ + ((1 : Int) : R)' in g and all(x in g for x in ['lookup18_41 a','d18_g_carry a','prefix_g a'])
assert G.split(':= by',1)[0].count('.castSucc')==31 and '((32 : Int) : R) * base a * (base a ^ (5 : Nat)) ^ (5 ^ 38 : Nat)' in G and all(x in G for x in ['lookup18_41 a','d18_G_carry a','prefix_G a'])
nodes=(d/'research/nine-seed38-jones-named-prefix-check/src/DiophantineConsistency/Norm38MacroPrefixes.lean').read_text()
for j in range(42,46):assert f'def d{j} : Dag {j} := .snoc d{j-1} ' in nodes
assert 'theorem recipe_eq_named : Norm38MacroRecipe.recipe = d45' in nodes

r=subprocess.run([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],capture_output=True,text=True,check=True,timeout=300);o=json.loads(r.stdout);assert not r.stderr and o['status']=='PASS_NO_LEAN_PREFLIGHT' and o['stage_count']==1
print(json.dumps({'status':'PASS','preflight':o,'scope':'d41 to recipe path and g/G values source; no Lean replay'},indent=2,sort_keys=True))
