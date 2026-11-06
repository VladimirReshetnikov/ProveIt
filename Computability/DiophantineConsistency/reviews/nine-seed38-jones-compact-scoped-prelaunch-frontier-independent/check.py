import hashlib,json,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
D=Path(__file__).resolve().parents[2];p=D/'research/nine-seed38-jones-compact-scoped-check'
def sha(x):return hashlib.sha256(Path(x).read_bytes()).hexdigest()
pins={'run.py':'f06833fb20298fc535224c31de13c05c7b976b8743446e8ddb1a20b6bbc87c04','provider_preflight.py':'b669d1ccf555e46a7f0c48f9cb95762b459c3e7f34def69c9fda2feb9d4548a6','source-manifest.json':'86a47134a0094864afd9c0f87e5bb1e77d988c1cf22076e1879fd4ea42ec863a','src/DiophantineConsistency/Norm38MacroScoped.lean':'db7aef04c0088a9e579d8f703489c366fd1e6207edfc37413a20e72fd4b27ba2'}
for k,h in pins.items():assert sha(p/k)==h,k
src=(p/'src/DiophantineConsistency/Norm38MacroScoped.lean').read_text();assert 'theorem recipe_well_scoped : Norm38MacroRecipe.WellScopedTarget := by\n  decide' in src and '#print axioms recipe_well_scoped' in src and 'SemanticTarget' not in src
imports=json.loads((p/'source-manifest.json').read_text())['rows'][0]['imports'];assert imports==['DiophantineConsistency.Norm38MacroRecipe'];s=json.loads(subprocess.check_output([sys.executable,'-I','-S','-B',str(p/'provider_preflight.py')],timeout=300));assert s['status']=='PASS_POINT_IN_TIME_PROVIDER_SURVEY' and s['selected'][imports[0]]['sha256']=='c1c8213d2c752991e7404820521fcd6466511b187a0648c000894254f4bd7129'
r=json.loads(subprocess.check_output([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],timeout=300));assert r['status']=='PASS_NO_LEAN_PREFLIGHT' and r['stage_count']==1
print(json.dumps({'status':'PASS_PRELAUNCH_ONLY','pins':pins,'direct_producer':s['selected'][imports[0]],'scope':'Proposed boolean binder-scoping theorem only, no semantic equality or verified JSON serialization.'},indent=2,sort_keys=True))
