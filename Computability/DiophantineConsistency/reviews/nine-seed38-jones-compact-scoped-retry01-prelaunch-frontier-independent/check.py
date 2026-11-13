import hashlib,json,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
D=Path(__file__).resolve().parents[2];p=D/'research/nine-seed38-jones-compact-scoped-retry01';old=D/'research/nine-seed38-jones-compact-scoped-check'
def sha(x):return hashlib.sha256(Path(x).read_bytes()).hexdigest()
pins={'run.py':'99f0c47171d85b425bba573e486a7734e03b7a700160f4046282c2de33658c07','provider_preflight.py':'b669d1ccf555e46a7f0c48f9cb95762b459c3e7f34def69c9fda2feb9d4548a6','source-manifest.json':'92eba81d54d66f299601890005f7eb62e56cb3bd38714aac60dbd49c725b8a94','src/DiophantineConsistency/Norm38MacroScoped.lean':'c69c030ac6de7d911efc08273746f993731861a89ad8e13419640526a4f6a4f4'}
for k,h in pins.items():assert sha(p/k)==h,k
before=(old/'src/DiophantineConsistency/Norm38MacroScoped.lean').read_text();after=(p/'src/DiophantineConsistency/Norm38MacroScoped.lean').read_text();a=':= by\n  decide\n';b=':= by\n  change Norm38MacroRecipe.recipe.scoped = true\n  decide\n';assert before.count(a)==1 and before.replace(a,b)==after
assert sha(old/'provider_preflight.py')==sha(p/'provider_preflight.py') and sha(old/'attempt01/state.json')=='d6b5fbbc57edfa3fe67537b77402ebe72e196a2557de728bbbe287e508167cd2' and sha(old/'attempt01/Norm38MacroScoped-compile.txt')=='8ed78797e0ce65bb0b33b9b0e924c0c17a2f387f51ddc113db0ab7985caf77e7'
imports=json.loads((p/'source-manifest.json').read_text())['rows'][0]['imports'];assert imports==['DiophantineConsistency.Norm38MacroRecipe'];s=json.loads(subprocess.check_output([sys.executable,'-I','-S','-B',str(p/'provider_preflight.py')],timeout=300));assert s['status']=='PASS_POINT_IN_TIME_PROVIDER_SURVEY' and s['selected'][imports[0]]['sha256']=='c1c8213d2c752991e7404820521fcd6466511b187a0648c000894254f4bd7129'
r=json.loads(subprocess.check_output([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],timeout=300));assert r['status']=='PASS_NO_LEAN_PREFLIGHT' and r['stage_count']==1
print(json.dumps({'status':'PASS_PRELAUNCH_ONLY','pins':pins,'direct_producer':s['selected'][imports[0]],'scope':'Explicit target exposure only, prior failure and point provider checks; no Lean scoping theorem or semantic equality.'},indent=2,sort_keys=True))
