import hashlib,json,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
D=Path(__file__).resolve().parents[2];p=D/'research/nine-seed38-jones-compact-language-check';draft=D/'research/nine-seed38-jones-compact-lean-draft/Norm38MacroLanguage.lean'
def sha(x):return hashlib.sha256(Path(x).read_bytes()).hexdigest()
pins={'run.py':'59b2ec4a8bb5a55da27aafcdb0bbd3a1881d81f4d4d9dba15e22eb0b8a574f44','provider_preflight.py':'45ae572c326ad285b64ad5cab6e4206b2ee4568202d7431903f707726554cb35','source-manifest.json':'2be6dd4be011ed0948971a417f06878ae19b76f2924bf6bdb8ef4108fd08dcd5','src/DiophantineConsistency/Norm38MacroLanguage.lean':'18ecac5f271aafd336133d48d8fdf9357e06dda7ca649712a801e71097a0e624'}
for k,h in pins.items():assert sha(p/k)==h,k
assert sha(draft)==pins['src/DiophantineConsistency/Norm38MacroLanguage.lean'];t=draft.read_text()
for x in ['inductive NExpr where','inductive Term (n : Nat) where','| ref (i : Fin n)','inductive Dag : Nat → Type where','prefix.scoped && entry.scoped false false','a.eval r k - b.eval r k','(indexZ seed 0 : R)','(indexY seed 0 : R)','(pCoefficient seed k : R)','∑ j ∈ Finset.range (upper.eval r k), body.eval a prev j k','∑ k\' ∈ codingStar 38 4, body.eval a prev r k\'','Fin.snoc prev (entry.eval a prev 0 (fun _ => 0))']:assert x in t,x
imports=json.loads((p/'source-manifest.json').read_text())['rows'][0]['imports'];assert imports==['DiophantineConsistency.Norm38NamedFormula'];s=json.loads(subprocess.check_output([sys.executable,'-I','-S','-B',str(p/'provider_preflight.py')],timeout=300));assert s['status']=='PASS_POINT_IN_TIME_PROVIDER_SURVEY' and s['selected'][imports[0]]['sha256']=='f628947fecd14dec5840ed18aa4b362c8e1173e6cf4fbdb60722c428e23b2725'
r=json.loads(subprocess.check_output([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],timeout=300));assert r['status']=='PASS_NO_LEAN_PREFLIGHT' and r['stage_count']==1
print(json.dumps({'status':'PASS_PRELAUNCH_ONLY','pins':pins,'direct_producer':s['selected'][imports[0]],'scope':'Proposed macro language source and point provider checks; no Lean compilation, recipe, semantic theorem or JSON binding.'},indent=2,sort_keys=True))
