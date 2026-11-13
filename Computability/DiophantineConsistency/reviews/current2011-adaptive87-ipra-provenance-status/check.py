from pathlib import Path
from hashlib import sha256
import json,os,subprocess,sys,tempfile
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode and not sys.flags.optimize
D=Path('reviews/current2011-adaptive87-ipra-provenance-status')
for p,h in json.loads((D/'pins.json').read_text()).items():assert sha256(Path(p).read_bytes()).hexdigest()==h,p
snapshot=Path('reviews/ipra-adaptive-fixed-snapshot-prefix/sources/DiophantineConsistency')
for n in ['IPRA87TranslatedRefutation','IPRAAdaptiveNativeZFC','AdaptiveFirstRootFactor87Literal']:
 assert (snapshot/(n+'.lean')).read_bytes()==(Path('Lean/DiophantineConsistency')/(n+'.lean')).read_bytes(),n
source=(Path('Lean/DiophantineConsistency/IPRAAdaptiveNativeZFC.lean')).read_text()
for t in ['def noZero87','theorem equivalence87 : nativeTheory ⊢ noZero87','IPRA87TranslatedRefutation.translated_refutation','IPRABoundedRhoZFC.zfcEquiv']:assert t in source,t
literal=Path('Lean/DiophantineConsistency/AdaptiveFirstRootFactor87Literal.lean').read_text()
assert 'def expression87 : Expr (Fin 13) := expressionAt87 CurrentWindowCarry2011.ports' in literal
assert 'positiveShift expression87' in literal
states=[json.loads(Path('reviews/ipra-adaptive-native-fixed-continuation-verification/'+x+'-state.json').read_text()) for x in ['author','independent']]
comparison=json.loads(Path('reviews/ipra-adaptive-native-fixed-continuation-verification/receipt.json').read_text());assert comparison['status']=='MATCHED_PASS'
mods=['DiophantineConsistency.IPRA87TranslatedRefutation','DiophantineConsistency.IPRAAdaptiveNativeZFC','DiophantineConsistency.IPRAAdaptiveNativeZFCChecks'];extracted={}
for mod in mods:
 rows=[]
 for state in states:
  assert state['status']=='PASS';rs=[r for r in state['records'] if r.get('name')==mod];assert len(rs)==1 and rs[0]['exit']==0;rows.append(rs[0])
 assert rows[0]['object_sha256']==rows[1]['object_sha256'] and rows[0]['log_sha256']==rows[1]['log_sha256']
 assert {k:v['sha256'] for k,v in rows[0]['direct_imports'].items()}=={k:v['sha256'] for k,v in rows[1]['direct_imports'].items()}
 extracted[mod]={'object_sha256':rows[0]['object_sha256'],'log_sha256':rows[0]['log_sha256'],'direct_imports':{k:v['sha256'] for k,v in rows[0]['direct_imports'].items()}}
 assert any(x['name']==mod and x['object_sha256']==rows[0]['object_sha256'] for x in comparison['matched_rows'])
prior=json.loads(Path('reviews/ipra87-translationcore-followup-translated-join-independent-pass/state.json').read_text());rs=[r for r in prior['records'] if r.get('module')=='DiophantineConsistency.IPRA87TranslatedRefutation'];assert prior['status']=='PASS' and len(rs)==1
assert rs[0]['object_sha256']==extracted[mods[0]]['object_sha256']
log=Path('reviews/ipra-adaptive-native-fixed-continuation-verification/independent-logs/DiophantineConsistency_IPRAAdaptiveNativeZFCChecks.log').read_text()
assert 'IPRAAdaptiveNativeZFC.equivalence87' in log and '[propext, Classical.choice, Quot.sound]' in log
for script,expected in [('research/current2011-adaptive87-ipra-standalone-source-draft/check.py','research/current2011-adaptive87-ipra-standalone-source-draft/receipt.json'),('research/adaptive-first-root-factor87/audit.py','research/adaptive-first-root-factor87/AUDIT.json'),('research/adaptive-direct-ordinate86/verify_degree87_parent.py','research/adaptive-direct-ordinate86/verify_degree87_parent.out')]:
 out=subprocess.run([sys.executable,'-I','-S','-B',script],check=True,stdout=subprocess.PIPE,timeout=30).stdout
 assert out==Path(expected).read_bytes(),script
with tempfile.TemporaryDirectory(prefix='shear87-literal-audit-') as temp:
 path=Path(temp)/'literal.lean';env=os.environ.copy();env['ADAPTIVE_FACTOR87_LEAN_OUT']=str(path)
 subprocess.run([sys.executable,'-I','-S','-B','research/adaptive-first-root-factor87/build_literal_lean.py'],check=True,stdout=subprocess.PIPE,timeout=30,env=env)
 assert path.read_bytes()==(snapshot/'AdaptiveFirstRootFactor87Literal.lean').read_bytes()
manifest=json.loads(Path('reviews/ipra-adaptive-native-fixed-continuation/manifest.json').read_text());root=Path('../..');drift=[];missing=[]
for name,relative in manifest['source_files'].items():
 p=root/relative
 if not p.is_file():missing.append(name);continue
 actual=sha256(p.read_bytes()).hexdigest();expected=manifest['source_sha256'][name]
 if actual!=expected:drift.append({'module':name,'snapshot_sha256':expected,'workspace_sha256':actual})
print(json.dumps({'pins_sha256':sha256((D/'pins.json').read_bytes()).hexdigest(),'paired_historical_state':'MATCHED_PASS','endpoint_records':extracted,'earlier_translation_object_matches':True,'same_literal_and_two_endpoint_source_hashes':True,'fixed_graph_operations':87,'exact_external_degree':51,'graph_and_degree_checks_reproduced':True,'source_generator_reproduced':True,'historical_manifest_sources':len(manifest['source_files']),'workspace_source_drift':sorted(drift,key=lambda x:x['module']),'workspace_sources_missing':sorted(missing),'lean_executed':False,'current_source_or_provider_authenticated':False},sort_keys=True,indent=2))
