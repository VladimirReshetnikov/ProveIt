import hashlib,json,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
D=Path(__file__).resolve().parents[2];p=D/'research/nine-seed38-jones-compact-recipe-check';draft=D/'research/nine-seed38-jones-compact-lean-draft/Norm38MacroRecipe.lean'
def sha(x):return hashlib.sha256(Path(x).read_bytes()).hexdigest()
pins={'run.py':'aec7254844545b2ca54818bd3097fac4badf8601e112a8e5a61f0ee7d13de0b6','provider_preflight.py':'5417c59e8fc74d419a55fc08d52dbc30c6d6efb32898bd26f758a72a5b9330de','source-manifest.json':'0d0203227fc368c4a24731bcd67c6c48798165604df2e4eb27c28253dc7a9092','src/DiophantineConsistency/Norm38MacroRecipe.lean':'3756c5e056e9bfedd28aa1fca5d5aa01c6bbde8163332c70abced196cf6d3979'}
for k,h in pins.items():assert sha(p/k)==h,k
assert sha(draft)==pins['src/DiophantineConsistency/Norm38MacroRecipe.lean'];t=draft.read_text();assert 'def recipe : Dag 45' in t and 'def WellScopedTarget : Prop := recipe.scoped = true' in t and 'def SemanticTarget : Prop :=' in t and 'recipe.values a (Fin.last 44) = Norm38IPRAEndpoint.expression.evalRing a' in t and 'theorem SemanticTarget' not in t
subprocess.run([sys.executable,'-I','-S','-B',str(D/'reviews/nine-seed38-jones-compact-lean-draft-frontier-independent/check.py')],check=True,stdout=subprocess.DEVNULL,timeout=60)
imports=json.loads((p/'source-manifest.json').read_text())['rows'][0]['imports'];assert imports==['DiophantineConsistency.Norm38MacroLanguage'];s=json.loads(subprocess.check_output([sys.executable,'-I','-S','-B',str(p/'provider_preflight.py')],timeout=300));assert s['status']=='PASS_POINT_IN_TIME_PROVIDER_SURVEY' and s['selected'][imports[0]]['sha256']=='7031d85f55adb8f82f96686c300443da2adf4eeb30ae743fb6f42a08509e8d65'
r=json.loads(subprocess.check_output([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],timeout=300));assert r['status']=='PASS_NO_LEAN_PREFLIGHT' and r['stage_count']==1
print(json.dumps({'status':'PASS_PRELAUNCH_ONLY','pins':pins,'direct_producer':s['selected'][imports[0]],'independently_decoded_nodes':45,'scope':'Recipe elaboration only; target propositions unproved, no Lean semantic theorem or verified JSON serialization.'},indent=2,sort_keys=True))
