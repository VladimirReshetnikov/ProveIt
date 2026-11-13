import hashlib,json,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
D=Path(__file__).resolve().parents[2];p=D/'research/nine-seed38-jones-named-formula-check';draft=D/'research/nine-seed38-jones-named-formula-draft/Norm38NamedFormula.lean'
def sha(x):return hashlib.sha256(Path(x).read_bytes()).hexdigest()
pins={'run.py':'0011f65367a47fd89d8ee77e4d1412589df2d0ce6b3df8e44f29561e72cf663a','provider_preflight.py':'900f407ae740f2a5f17b139a8639a7c457608fe8c46bbe97a5d085f30f13b386','source-manifest.json':'c89b0797e66018de9bb0bcd12203d917c98e9c4bca62c15c191e8eaea631342c','src/DiophantineConsistency/Norm38NamedFormula.lean':'a5a8db6833252881c37016f3b28e006168db45a8119074b04572c8341d2593e6'}
for k,h in pins.items():assert sha(p/k)==h,k
assert sha(draft)==pins['src/DiophantineConsistency/Norm38NamedFormula.lean'];src=draft.read_text()
for x in ['Norm38IPRAEndpoint.expression.evalRing a','let ν := 38','let seed := SharingSeed38.seed CurrentWindowCarry2011.ports','let aa : Fin 10 → R := Fin.cons 1 a','ModelJonesSyntax.evalRing_expression','ModelJonesSyntax.mapVars_syntaxVars']:assert x in src
imports=['DiophantineConsistency.Norm38IPRAEndpoint','DiophantineConsistency.ModelJonesSyntax'];rows=json.loads((p/'source-manifest.json').read_text())['rows'];assert len(rows)==1 and rows[0]['imports']==imports
s=json.loads(subprocess.check_output([sys.executable,'-I','-S','-B',str(p/'provider_preflight.py')],timeout=300));assert s['status']=='PASS_POINT_IN_TIME_PROVIDER_SURVEY' and all(k in s['selected'] for k in imports)
assert s['selected'][imports[0]]['sha256']=='570952bced71ff043c7fa9f0f84af3e99b8a6fea2f373651f12c01e7e6c72125' and s['selected'][imports[1]]['sha256']=='ca320ae03c5aece08482a0eb125d58c12d371ce524cce685428b0550a96c5171'
r=json.loads(subprocess.check_output([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],timeout=300));assert r['status']=='PASS_NO_LEAN_PREFLIGHT' and r['stage_count']==1
print(json.dumps({'status':'PASS_PRELAUNCH_ONLY','pins':pins,'direct_producers':{k:s['selected'][k] for k in imports},'seed_producers':{k:v for k,v in s['selected'].items() if 'SharingSeed38' in k},'scope':'Ring evaluation client source and point-in-time providers, no Lean compilation or human formula binding.'},indent=2,sort_keys=True))
