import hashlib,json,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
D=Path(__file__).resolve().parents[2];p=D/'research/nine-seed38-jones-compact-language-retry01';old=D/'research/nine-seed38-jones-compact-language-check'
def sha(x):return hashlib.sha256(Path(x).read_bytes()).hexdigest()
pins={'run.py':'1c74fc56546e381c1ea5f41031e42ff9cf55a8ef151ee811b1c5b1fb5f6e5396','provider_preflight.py':'45ae572c326ad285b64ad5cab6e4206b2ee4568202d7431903f707726554cb35','source-manifest.json':'0ab0cd9a5eab513f69ba7a0c446f204d48ecc4c2fc9b165b3154f376b62e13c1','src/DiophantineConsistency/Norm38MacroLanguage.lean':'8b25a5ac8047503064f7d044c0d17f36f39b458902b8e927c8ec685fc8677b3f'}
for k,h in pins.items():assert sha(p/k)==h,k
before=(old/'src/DiophantineConsistency/Norm38MacroLanguage.lean').read_text();after=(p/'src/DiophantineConsistency/Norm38MacroLanguage.lean').read_text()
for a,b in [('(prefix : Dag n)','(prior : Dag n)'),('.snoc prefix entry','.snoc prior entry'),('prefix.scoped','prior.scoped'),('prefix.values','prior.values')]:assert a in before;before=before.replace(a,b)
assert before==after
assert sha(old/'provider_preflight.py')==sha(p/'provider_preflight.py') and sha(old/'attempt01/state.json')=='f68968f4fae77941198bf7726512df92b81a9be0a25f797e21a17cfed390f258' and sha(old/'attempt01/Norm38MacroLanguage-compile.txt')=='3c8396391cb87aebe9782efe5c13f6ed40c8d878c0028998bfd9a32e8ace0627'
imports=json.loads((p/'source-manifest.json').read_text())['rows'][0]['imports'];assert imports==['DiophantineConsistency.Norm38NamedFormula'];s=json.loads(subprocess.check_output([sys.executable,'-I','-S','-B',str(p/'provider_preflight.py')],timeout=300));assert s['status']=='PASS_POINT_IN_TIME_PROVIDER_SURVEY' and s['selected'][imports[0]]['sha256']=='f628947fecd14dec5840ed18aa4b362c8e1173e6cf4fbdb60722c428e23b2725'
r=json.loads(subprocess.check_output([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],timeout=300));assert r['status']=='PASS_NO_LEAN_PREFLIGHT' and r['stage_count']==1
print(json.dumps({'status':'PASS_PRELAUNCH_ONLY','pins':pins,'direct_producer':s['selected'][imports[0]],'scope':'Exact local binder rename, prior failure and point provider checks; no Lean language object or graph theorem.'},indent=2,sort_keys=True))
