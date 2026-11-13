import hashlib,json,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
D=Path(__file__).resolve().parents[2];p=D/'research/nine-seed38-jones-compact-semantics-cut-check';draft=D/'research/nine-seed38-jones-compact-semantics-cut-draft/Norm38MacroCuts.lean'
def sha(x):return hashlib.sha256(Path(x).read_bytes()).hexdigest()
pins={'run.py':'a0f2efd25793092ca45030dccd35a5cfe0bcad8675d9c03c4fcfeee2830b7f9f','provider_preflight.py':'5417c59e8fc74d419a55fc08d52dbc30c6d6efb32898bd26f758a72a5b9330de','source-manifest.json':'db21b2af124d752fadde81efe0328c425bc1f9eb0a26a08ea25e53a120e025cf','src/DiophantineConsistency/Norm38MacroCuts.lean':'de5a30d88de5f15a6b08f9a450e2b430104928dae8af67888f4bd92fb578da9d'}
for k,h in pins.items():assert sha(p/k)==h,k
assert sha(draft)==pins['src/DiophantineConsistency/Norm38MacroCuts.lean'];src=draft.read_text()
for x in ['theorem snoc_previous','(Dag.snoc d t).values a i.castSucc = d.values a i','theorem snoc_last','(Dag.snoc d t).values a (Fin.last n) = t.eval a (d.values a) 0 (fun _ => 0)','theorem eval_range','∑ j ∈ Finset.range (upper.eval r k), body.eval a prev j k','theorem eval_star',"∑ k' ∈ codingStar 38 4, body.eval a prev r k'",'#print axioms snoc_previous','#print axioms snoc_last','#print axioms eval_range','#print axioms eval_star']:assert x in src,x
assert 'SemanticTarget' not in src
imports=json.loads((p/'source-manifest.json').read_text())['rows'][0]['imports'];assert imports==['DiophantineConsistency.Norm38MacroLanguage'];s=json.loads(subprocess.check_output([sys.executable,'-I','-S','-B',str(p/'provider_preflight.py')],timeout=300));assert s['status']=='PASS_POINT_IN_TIME_PROVIDER_SURVEY' and s['selected'][imports[0]]['sha256']=='7031d85f55adb8f82f96686c300443da2adf4eeb30ae743fb6f42a08509e8d65'
r=json.loads(subprocess.check_output([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],timeout=300));assert r['status']=='PASS_NO_LEAN_PREFLIGHT' and r['stage_count']==1
print(json.dumps({'status':'PASS_PRELAUNCH_ONLY','pins':pins,'direct_producer':s['selected'][imports[0]],'scope':'Four generic DAG/sum equations only, no semantic graph theorem or verified JSON serialization.'},indent=2,sort_keys=True))
