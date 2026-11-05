#!/usr/bin/env python3
"""Independent read-only check of terminal client records and recipe text; no Lean."""
import hashlib,importlib.util,json,re
from pathlib import Path
ROOT=Path(__file__).resolve().parents[4]
TASK=ROOT/'Computability/DiophantineConsistency'
packet=TASK/'research/current14-mf-base-only-endpoint-attempt02'
old=TASK/'research/current14-literal-port-assembly/Current14LiteralPorts.lean'
lean=TASK/'Lean/DiophantineConsistency'
out=Path('/tmp/current14-mf-base-only-attempt02-20261104')
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def need(x,m):
 if not x:raise ValueError(m)
state=json.loads((out/'state.json').read_text())
need(state['status']=='PASS' and state['phase']=='complete','terminal status')
need(state['runner_sha256']=='fae89cf5ae51f4ae5b9fe87129be41b38d19b456398cb954af14951fd0f1f7a1'==sha(packet/'runner.py'),'runner pin')
records=state['records'];need([r['module'] for r in records]==['Current14LiteralPortsMF','StructuredEndpointMF'],'record names')
helper=TASK/'research/current14-printed-port-extension-driver-v3/guards.py'
need(sha(helper)=='e42ef7c73da49653b1d664b947c3a9ea5fa2ae78206d0988472a948a901fafc3','guard helper pin')
spec=importlib.util.spec_from_file_location('guards',helper);g=importlib.util.module_from_spec(spec);spec.loader.exec_module(g)
base=json.loads(Path('/tmp/current14-standard-fresh-build-20261104/state.json').read_text())
expected_deps=[{'Init','DiophantineConsistency.MFCurrentKernel2011','DiophantineConsistency.ArithmeticMaskData','DiophantineConsistency.MFPaper1982Digits'}, {'Init','Current14LiteralPortsMF','DiophantineConsistency.IPRAStandardCurrentEndpoint'}]
expected_reports=[['Current14LiteralPortsMF.'+x for x in ['beta_eq','mu_eq','omega_eq','K_eq','all_ports']],['Current14StructuredEndpointMF.recipe_endpoint']]
for idx,r in enumerate(records):
 name=r['module'];need(r['exit']==0,'exit')
 need(r['source_sha256']==sha(packet/(name+'.lean'))==sha(out/'src'/(name+'.lean')),'source')
 need(set(r['direct_inputs'])==expected_deps[idx],'direct dependencies')
 for field in ('log','stderr','deps_stdout','deps_stderr'):
  need(sha(r[field])==r[field+'_sha256'],'log digest '+field)
 for phase in ('deps_receipt','compile_receipt'):
  p=r[phase];need(p['exit']==0 and p['direct_child_reaped'] and p['session_drained'],'child receipt')
 need([x[0] for x in r['axiom_reports']]==expected_reports[idx],'report names')
 for _,axioms in r['axiom_reports']:
  need(set(x.strip() for x in axioms.split(','))<={'propext','Classical.choice','Quot.sound'},'axioms')
 log=Path(r['log']).read_text()+'\n'+Path(r['stderr']).read_text()
 need(not re.search(r'(?mi)^.*(?:error:|error\([^)]*\):|warning:)|\bsorryAx\b|\bsorry\b',log),'bad log')
 g.check_guard(r['direct_guards']);g.check_guard(r['output_guards'])
 for module,info in r['direct_inputs'].items():
  path=Path(info['path']);need(sha(path)==info['sha256'],'input digest')
  if module in base['outputs']:
   need(r['direct_guards'][str(path)]==base['outputs'][module][str(path)],'base producer mismatch')
  elif module=='Current14LiteralPortsMF':
   need(info['sha256']==records[0]['object_sha256'],'local producer mismatch')
  else:need(module=='Init' and info['sha256']==base['guarded_companions'][str(path)]['sha256'],'external producer mismatch')
 need(sha(out/'lib'/(name+'.olean'))==r['object_sha256'],'object digest')
oldtext=old.read_text();newtext=(packet/'Current14LiteralPortsMF.lean').read_text()
def definition(text,name):
 m=re.search(r'^def '+name+r'\b.*?(?=\n\n)',text,re.M|re.S);need(m is not None,'definition '+name);return m.group()
for name in ('beta','mu','omega','K'):
 need(definition(newtext,name)==definition(oldtext,name),'recipe differs '+name)
need(definition(newtext,'phi').replace('MF.CurrentKernel2011.geometric','CurrentKernel2011.geometric')==definition(oldtext,'phi'),'phi text differs')
geom='  ∑ j ∈ Finset.range n, x ^ j'
for name in ('MFCurrentKernel2011','CurrentKernel2011'):
 t=(lean/(name+'.lean')).read_text();need('def geometric {R : Type*} [Semiring R] (x : R) (n : ℕ) : R :=\n'+geom in t,'geometric body differs '+name)
need('def geometricInt (r : ℤ) (n : ℕ) : ℤ := ∑ j ∈ Finset.range n, r ^ j' in (lean/'CurrentMaskRecipes2011.lean').read_text(),'original G body')
need('abbrev G (n : ℕ) : ℤ := ∑ j ∈ Finset.range n, (rho : ℤ) ^ j' in newtext,'new G body')
endpoint=(packet/'StructuredEndpointMF.lean').read_text();core=(lean/'CurrentEquationSyntax2011.lean').read_text();native=(lean/'IPRACurrentNativeZFC.lean').read_text()
for fragment in ('p : Fin 4 → ℤ','positiveShift (expressionAt p)','e.splitNatural.1','e.splitNatural.2','standardTheory ⊢ noZeroAt p 🡘 ∼mappedNativeRefutation embedding','change standardTheory ⊢ noZero14','ipra_current_iff_consistency'):
 need(fragment in endpoint,'missing endpoint fragment '+fragment)
for fragment in ('expressionAt CurrentWindowCarry2011.ports','naturalExpression : Expr (Fin 14) := positiveShift expression','e.subst (fun i => Expr.var i + Expr.constant 1)'):
 need(fragment in core,'missing syntax fragment '+fragment)
need('naturalExpression.splitNatural.1' in native and 'naturalExpression.splitNatural.2' in native,'noZero14 sides')
result={'status':'PASS','scope':'Terminal client records and direct guards; recipe source comparison and endpoint theorem scope. No Lean launch, PDF parse, or independent full transitive proof reconstruction.', 'state_sha256':sha(out/'state.json'),'runner_sha256':sha(packet/'runner.py'),'first_object_sha256':records[0]['object_sha256'],'endpoint_object_sha256':records[1]['object_sha256'],'review_script_sha256':sha(__file__)}
print(json.dumps(result,sort_keys=True))
