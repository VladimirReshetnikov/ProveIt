import hashlib,json,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
D=Path(__file__).resolve().parents[2];p=D/'research/nine-seed38-jones-compact-first-node-check';draft=D/'research/nine-seed38-jones-compact-first-node-draft/Norm38MacroFirst.lean'
def sha(x):return hashlib.sha256(Path(x).read_bytes()).hexdigest()
pins={'run.py':'7c9de4d9127e308ce85d591cf3d81aaec3a6c93f26f545e6e0985b900dc2d3ad','provider_preflight.py':'b669d1ccf555e46a7f0c48f9cb95762b459c3e7f34def69c9fda2feb9d4548a6','source-manifest.json':'a3c07a5221b28d07b14a2e50794b90cfa07724fd12b7f0ccff7a28bac0d2b81f','src/DiophantineConsistency/Norm38MacroFirst.lean':'1904331aac21711865c0933a2cd441b9354650a63098fc5a9fb5a5d59462607d'}
for k,h in pins.items():assert sha(p/k)==h,k
assert sha(draft)==pins['src/DiophantineConsistency/Norm38MacroFirst.lean'];t=draft.read_text()
for x in ['theorem first_node {R : Type*} [CommRing R] (a : Fin 9 → R)','Norm38MacroRecipe.recipe.values a ⟨0, by decide⟩','((indexY Norm38MacroLanguage.seed 0 : Nat) : R) + ((1 : Int) : R) + a ⟨0, by decide⟩','  rfl','#print axioms first_node']:assert x in t,x
recipe=(D/'research/nine-seed38-jones-compact-lean-draft/Norm38MacroRecipe.lean').read_text();assert 'let d1 : Dag 1 := .snoc d0 (.add (.add (.fixedY) (.constant (1 : Int))) (.input ⟨0, by decide⟩))' in recipe
imports=json.loads((p/'source-manifest.json').read_text())['rows'][0]['imports'];assert imports==['DiophantineConsistency.Norm38MacroRecipe'];s=json.loads(subprocess.check_output([sys.executable,'-I','-S','-B',str(p/'provider_preflight.py')],timeout=300));assert s['status']=='PASS_POINT_IN_TIME_PROVIDER_SURVEY' and s['selected'][imports[0]]['sha256']=='c1c8213d2c752991e7404820521fcd6466511b187a0648c000894254f4bd7129'
r=json.loads(subprocess.check_output([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],timeout=300));assert r['status']=='PASS_NO_LEAN_PREFLIGHT' and r['stage_count']==1
print(json.dumps({'status':'PASS_PRELAUNCH_ONLY','pins':pins,'direct_producer':s['selected'][imports[0]],'scope':'First concrete recipe node only; no full graph semantics or JSON binding.'},indent=2,sort_keys=True))
