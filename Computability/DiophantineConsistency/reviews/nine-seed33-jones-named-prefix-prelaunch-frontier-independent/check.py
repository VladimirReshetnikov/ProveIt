#!/usr/bin/env python3
import hashlib,json,re
from pathlib import Path
D=Path(__file__).resolve().parents[2];P=D/'research/nine-seed33-jones-named-prefix-check';sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert sha(P/'run.py')=='792eec9d7ef1ae4675c04b9bbc002a59592c4a8d493dd1260b8ae6229304e576' and sha(P/'source-manifest.json')=='1f7878c02813f49a10e188a6827a7b5b6f7534e198176eb9b0ef615efc02651a'
m=json.loads((P/'source-manifest.json').read_text())['rows'];assert len(m)==1 and m[0]['module']=='DiophantineConsistency.Sign33MacroPrefixes' and m[0]['imports']==['DiophantineConsistency.Sign33MacroRecipe'];p=P/'src/DiophantineConsistency/Sign33MacroPrefixes.lean';assert sha(p)==m[0]['source_sha256']=='0d78f54214e3c0a2a83dce4062385ec050494f288797bb02cb59ac2cd6a0af8d'
r=(D/'research/nine-seed33-jones-compact-recipe-light-draft/Sign33MacroRecipeLight.lean').read_text();s=p.read_text();lets=re.findall(r'^  let d(\d+) : Dag (\d+) := (.*)$',r,re.M);defs=re.findall(r'^def d(\d+) : Dag (\d+) := (.*)$',s,re.M);assert len(lets)==len(defs)==46 and lets==defs and [(int(a),int(b)) for a,b,_ in lets]==[(i,i) for i in range(46)] and lets[0][2]=='.nil'
for i in range(1,46):assert lets[i][2].startswith(f'.snoc d{i-1} ')
assert 'theorem recipe_eq_named : Sign33MacroRecipe.recipe = d45 := by\n  rfl' in s and '#print axioms recipe_eq_named' in s
print(json.dumps({'status':'PASS_STATIC','scope':'46 mechanically named prefixes and proposed Lean recipe=d45 identity only; no evaluator/JSON equality'}))
