#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
d=Path(__file__).resolve().parents[2];p=d/'research/nine-seed38-jones-prefix-path18-45-check';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
for n,h in {'run.py':'349b1d0faf57671dce58890e3ac7decd574080ee37b66a89cd7e55c45ce0af4f','provider_preflight.py':'dbda54c9db1abae2033aceda248770b58f60d2128be07d9b0bf010230b9b53f0','source-manifest.json':'ae8440e8db19fc0cf203448d1aadf61550b008add8f3ac41d80c4bedc66fdf83','src/DiophantineConsistency/Norm38MacroPath18to45.lean':'046e61d86f88b61d713475b1355d3fa9692547a9469928cba09f644d53229c6e'}.items():assert sha(p/n)==h
s=(p/'src/DiophantineConsistency/Norm38MacroPath18to45.lean').read_text();rows=json.loads((p/'source-manifest.json').read_text())['rows'];assert len(rows)==1 and rows[0]['source_sha256']=='046e61d86f88b61d713475b1355d3fa9692547a9469928cba09f644d53229c6e';assert re.findall(r'^import ([\w.]+)$',s,re.M)==rows[0]['imports']==['DiophantineConsistency.Norm38MacroPath18to41'];assert re.findall(r'^theorem (\w+)',s,re.M)==['path18_45','lookup18_45','lookup_recipe18'];assert re.findall(r'^#print axioms (\w+)',s,re.M)==['path18_45','lookup18_45','lookup_recipe18']
theorem=s.split('theorem path18_45',1)[1].split('theorem lookup18_45',1)[0];assert 'PrefixPath d18 d45' in theorem and theorem.count('.castSucc')==27 and theorem.count('PrefixPath.step')==4 and theorem.count('Dag.snoc')==4 and 'path18_41' in theorem
lookup=s.split('theorem lookup18_45',1)[1].split('theorem lookup_recipe18',1)[0];assert 'd45.values a ' in lookup and '= d18.values a i' in lookup and lookup.count('.castSucc')==27 and 'lookup path18_45 a i' in lookup
nodes=(d/'research/nine-seed38-jones-named-prefix-check/src/DiophantineConsistency/Norm38MacroPrefixes.lean').read_text()
for j in range(42,46):assert f'def d{j} : Dag {j} := .snoc d{j-1} ' in nodes

transfer=s.split('theorem lookup_recipe18',1)[1].split('#print',1)[0];assert 'Norm38MacroRecipe.recipe.values a ' in transfer and transfer.count('.castSucc')==27 and '= d18.values a i' in transfer and 'rw [recipe_eq_named]' in transfer and 'exact lookup18_45 a i' in transfer
assert 'theorem recipe_eq_named : Norm38MacroRecipe.recipe = d45' in nodes
r=subprocess.run([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],capture_output=True,text=True,check=True,timeout=300);o=json.loads(r.stdout);assert not r.stderr and o['status']=='PASS_NO_LEAN_PREFLIGHT' and o['stage_count']==1
print(json.dumps({'status':'PASS','preflight':o,'scope':'concrete full recipe path source and point-provider review; no Lean replay'},indent=2,sort_keys=True))
