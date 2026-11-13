#!/usr/bin/env python3
"""Read-only review of translated endpoint recorded artifacts and theorem source."""
import hashlib,importlib.util,json,re
from pathlib import Path
ROOT=Path(__file__).resolve().parents[4]; TASK=ROOT/'Computability/DiophantineConsistency'
p=TASK/'research/current14-mf-translated-endpoint'; lean=TASK/'Lean/DiophantineConsistency'
out=Path('/tmp/current14-mf-translated-endpoint-attempt01-20261104')
prior=Path('/tmp/current14-mf-base-only-attempt02-20261104')
def sha(x):return hashlib.sha256(Path(x).read_bytes()).hexdigest()
def need(x,msg):
 if not x:raise ValueError(msg)
s=json.loads((out/'state.json').read_text());need(s['status']=='PASS' and s['phase']=='complete','status')
need(s['runner_sha256']==sha(p/'runner.py')=='8ce9ef6199d5dc9b4d51f2666fac75b8a934692f261bfede177b64668b1aee9a','runner')
need(s['initial']['prior_state_sha256']==sha(prior/'state.json')=='464b231aaa0e6348e626e8e5fca2e84f283adc36e56b8daac5360124efe5dc98','prior state')
need(len(s['records'])==1,'record count');r=s['records'][0];need(r['module']=='TranslatedEndpointMF' and r['exit']==0,'client')
need(r['source_sha256']==sha(p/'TranslatedEndpointMF.lean')==sha(out/'src/TranslatedEndpointMF.lean')=='55dc65a31ea0c36927544317485eecb59e4e6e702c3067715da2a2f1241c4f8d','source')
for field in ('log','stderr','deps_stdout','deps_stderr'):need(sha(r[field])==r[field+'_sha256'],'log '+field)
for phase in ('deps_receipt','compile_receipt'):
 x=r[phase];need(x['exit']==0 and x['direct_child_reaped'] and x['session_drained'],'child '+phase)
need(r['axiom_reports']==[['Current14TranslatedEndpointMF.recipe_translated_endpoint','propext, Classical.choice, Quot.sound']],'axioms')
log=Path(r['log']).read_text()+'\n'+Path(r['stderr']).read_text();need(not re.search(r'(?mi)^.*(?:error:|error\([^)]*\):|warning:)|\bsorryAx\b|\bsorry\b',log),'bad log')
helper=TASK/'research/current14-printed-port-extension-driver-v3/guards.py'
need(sha(helper)=='e42ef7c73da49653b1d664b947c3a9ea5fa2ae78206d0988472a948a901fafc3','guard helper')
spec=importlib.util.spec_from_file_location('guards',helper);g=importlib.util.module_from_spec(spec);spec.loader.exec_module(g)
g.check_guard(r['direct_guards']);g.check_guard(r['output_guards'])
need(sha(out/'lib/TranslatedEndpointMF.olean')==r['object_sha256'],'object')
base=json.loads(Path('/tmp/current14-standard-fresh-build-20261104/state.json').read_text());pr=json.loads((prior/'state.json').read_text());parents={x['module']:x for x in pr['records']}
need(set(r['direct_inputs'])=={'Init','Current14LiteralPortsMF','StructuredEndpointMF','DiophantineConsistency.IPRAStandardCurrentEndpoint'},'dependency names')
for module,info in r['direct_inputs'].items():
 path=Path(info['path']);need(sha(path)==info['sha256'],'direct input digest')
 if module in parents:need(info['sha256']==parents[module]['object_sha256'] and r['direct_guards'][str(path)]==parents[module]['output_guards'][str(path)],'prior object mismatch')
 elif module in base['outputs']:need(r['direct_guards'][str(path)]==base['outputs'][module][str(path)],'base mismatch')
 else:need(module=='Init' and info['sha256']==base['guarded_companions'][str(path)]['sha256'],'Init mismatch')
t=(p/'TranslatedEndpointMF.lean').read_text()
for fragment in ('∃ p : Fin 4 → ℤ','p 0 = Current14LiteralPortsMF.beta','(p 1 : ℚ) = Current14LiteralPortsMF.K','p 2 = Current14LiteralPortsMF.mu','p 3 = Current14LiteralPortsMF.omega','standardTheory ⊢ noZeroAt p 🡘 (Semiformula.lMap embedding sourceSentence)ᴺ','⟨CurrentWindowCarry2011.ports, ?_⟩','IPRAStandardCurrentEndpoint.ipra_current_iff_translated_consistency'):
 need(fragment in t,'source '+fragment)
source=(lean/'FoundationZFCConsistencyNat.lean').read_text()
need('def sourceSentence : ArithmeticSentence :=' in source and '(LO.FirstOrder.SetTheory.ZermeloFraenkelChoice : LO.FirstOrder.SetTheory).consistent' in source,'source consistency')
base_endpoint=(lean/'IPRAStandardCurrentEndpoint.lean').read_text()
need('noZero14 🡘 ∼mappedNativeRefutation embedding' in base_endpoint and 'noZero14 🡘 (Semiformula.lMap embedding sourceSentence)ᴺ' in base_endpoint,'distinct endpoint forms')
result={'status':'PASS','scope':'Recorded translated endpoint artifacts, direct producer guards, source theorem shape. No Lean rerun or PDF parsing. Outer runner exit is separate observation.','state_sha256':sha(out/'state.json'),'runner_sha256':sha(p/'runner.py'),'object_sha256':r['object_sha256'],'review_script_sha256':sha(__file__)}
print(json.dumps(result,sort_keys=True))
