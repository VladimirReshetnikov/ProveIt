#!/usr/bin/env python3
"""Audit exact literal bindings, residue controls and bounded replay artifacts."""
import hashlib,itertools,json,os,re,subprocess,sys
from pathlib import Path
if not __debug__:raise RuntimeError('independent audit requires assertions enabled')
HERE=Path(__file__).resolve().parent;ROOT=HERE.parents[3];BASE=ROOT/'Computability/DiophantineConsistency';TASK=BASE/'research/ordinary12-ipra-bridge/concrete-split-prototype';LIT=TASK.parent/'literal-prototype';MODEL=TASK.parent/'model-prototype';GRAPH=BASE/'research/ordinary-unit-products/p12_ordinary_degree70.json';ORIG=Path('/tmp/ipra-ordinary12-concrete-replay-01');FRESH=Path('/tmp/ipra-ordinary12-concrete-split-independent-replay-02');FRESH_RECEIPT=Path('/tmp/ipra-ordinary12-concrete-split-independent-replay-02-receipt.json');PARENT=Path('/tmp/ipra-aq29-fresh-project-pair');SNAP=Path('/tmp/ipra-aq29-fresh-source-closure-v2');PROVIDER=Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/build-all-receipt.json');PACKAGE=Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib');LEAN=Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean');PRIOR=BASE/'reviews/fresh-project-pair-independent-audit';LITAUDIT=BASE/'reviews/ordinary12-literal-prototype-independent-audit'
H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest();J=lambda p:json.loads(Path(p).read_text());RAW=lambda s:hashlib.sha256(s.encode()).hexdigest()
files=[Path(__file__),TASK/'Ordinary12ConcreteSplit.lean',TASK/'Ordinary12Patterns.lean',TASK/'check_binding.py',TASK/'replay.py',TASK/'replay-receipt.json',TASK/'README.md',TASK/'observations/initial.json',TASK/'observations/Ordinary12ConcreteSplit-warning.lean',LIT/'Ordinary12Literal.lean',LIT/'check_literal.py',MODEL/'replay_composed.py',GRAPH,FRESH_RECEIPT,PARENT/'pair-state.json',PARENT/'author/state.json',SNAP/'manifest.json',PROVIDER,LEAN,PRIOR/'receipt.json',PRIOR/'terminal-observation.json',LITAUDIT/'receipt.json',LITAUDIT/'terminal-observation.json']
before={str(p.resolve()):H(p) for p in files};assert H(TASK/'replay-receipt.json')=='97aa4b119f8b37a3afb8bb4cafc2c0b8e03db233eb734a67b1fe23ce8fa36572' and H(FRESH_RECEIPT)=='6445a4082638704c72067501a720ecc7cc571e6ae3ed88166e3b0db845306191'
assert H(TASK/'Ordinary12ConcreteSplit.lean')=='5e512b0cd623d0875523b55b56301692891942a8ab66561262b0f94462627548' and H(TASK/'Ordinary12Patterns.lean')=='5b37fb90f66d1ac0775018ddc7b05c26bf6c9bd4615ff794318613a97c31b25a'
assert H(LIT/'Ordinary12Literal.lean')=='23a22eebc33d262e1b4c134c6072e808c002aac31a627def951bc753d3e96709' and H(GRAPH)=='444c25b68fbfee600ae174cb5bad1931897a55ffe2f9570fd22f3281f6e97010'
for f in files[1:9]:assert hashlib.sha256(subprocess.check_output(['git','show','fa799eca80:'+str(f.relative_to(ROOT))],cwd=ROOT)).hexdigest()==H(f)
lit=(LIT/'Ordinary12Literal.lean').read_text();src=(TASK/'Ordinary12ConcreteSplit.lean').read_text();patterns=(TASK/'Ordinary12Patterns.lean').read_text();g=J(GRAPH)
def section(s):
 start='  let j : Expr';end='  -- END LITERAL GRAPH';assert s.count(start)==s.count(end)==1
 return s[s.index(start):s.index(end)+len(end)]
def binding(s):
 if section(s)!=section(lit):raise ValueError('graph section differs')
 for expected in ('  ⟨qm,Z,g41,U,a,c,Dstar,AN,oneQ,vn,den,Q⟩','firstPattern (parts p).qm (parts p).z (parts p).n','mainPattern (parts p).u (parts p).a (parts p).c (parts p).d','ordinaryPattern (parts p).an (parts p).x (parts p).y (parts p).den (parts p).q'):
  if s.count(expected)!=1:raise ValueError(('binding differs',expected))
binding(src)
rows=re.findall(r'^  let (\w+) := (\w+) ([+*\-]) (\w+)$',section(src),re.M);parsed=[[n,o,int(a) if a.isdecimal() else a,int(b) if b.isdecimal() else b] for n,a,o,b in rows];assert parsed==g['source'] and len(parsed)==100
assert len(g['witnesses'])==12 and g['fixed_numerals']==['beta','K0','MC','MF'] and g['output']=='P12'
# Exact theorem statement has only arbitrary integer ports, arbitrary model
# valuation and internal-zero hypothesis under the stated IΣ₁ model context.
assert 'variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]' in src
statement=' '.join(src.split('theorem literal_factor_units ',1)[1].split(':= by',1)[0].split())
assert statement==('(p : Fin 4 → ℤ) (v : Fin 12 → V) (h : InternalZero (literal p) v) : '
 '(pairEval (core p).first v).1 = (pairEval (core p).first v).2 + 1 ∧ '
 '(pairEval (core p).main v).1 = (pairEval (core p).main v).2 + 1 ∧ '
 '(pairEval (core p).ordinary v).1 = (pairEval (core p).ordinary v).2 + 1')
for x in ('apply three_factor_units (product_one_of_internal_zero p v h)','exact first_ne _ _ _ v','exact main_ne _ _ _ _ v','exact ordinary_ne _ _ _ _ _ v'):assert x in src
for x in ('theorem first_eq (p : Fin 4 → ℤ)', 'theorem main_eq (p : Fin 4 → ℤ)', 'theorem ordinary_eq (p : Fin 4 → ℤ)'):assert x in src
assert 'firstPattern (qm z n : Expr (Fin 12))' in patterns and 'mainPattern (u a c d : Expr (Fin 12))' in patterns and 'ordinaryPattern (an x y d q : Expr (Fin 12))' in patterns
mutations=[('let qm := J * beta','let qm := J + beta'),('⟨qm,Z,g41','⟨qm,Z,g40'),('firstPattern (parts p).qm','firstPattern (parts p).z'),('ordinaryPattern (parts p).an','ordinaryPattern (parts p).q')]
for a,b in mutations:
 assert src.count(a)==1
 try:binding(src.replace(a,b,1))
 except (ValueError,AssertionError):pass
 else:raise AssertionError(('binding mutation accepted',a))
# Independent finite residue verification, including changes that genuinely
# produce counterexamples when each decisive factor is altered.
patterns_mod=[(3,lambda q,z,n:1+z*z-(q**3*(q-1))**2*n),(4,lambda u,a,c,d:1+d*d-u*u*(1+(a*a+4*a+3)*c*c)),(4,lambda a,b,d,q:1+a*a-(q*d)*((2*b)*(2*b)))]
bad_mod=[(3,lambda q,z,n:1+z*z-q**6*n),(4,lambda u,a,c,d:1+d*d-u*u*(1+(a*a+4*a+2)*c*c)),(4,lambda a,b,d,q:1+a*a-(q*d)*(b*b))]
for n,fn in patterns_mod:assert all(fn(*x)%4!=3 for x in itertools.product(range(4),repeat=n))
for n,fn in bad_mod:assert any(fn(*x)%4==3 for x in itertools.product(range(4),repeat=n))
check=subprocess.run([sys.executable,str(TASK/'check_binding.py')],capture_output=True,text=True,timeout=60);assert check.returncode==0 and check.stdout.strip()=='PASS_CONCRETE_PARTS_BINDING 100 rows 12 parts 3 mutations rejected'
checkopt=subprocess.run([sys.executable,'-O',str(TASK/'check_binding.py')],capture_output=True,text=True,timeout=30);assert checkopt.returncode!=0 and 'checks require Python assertions enabled' in checkopt.stderr
warning=(TASK/'observations/Ordinary12ConcreteSplit-warning.lean').read_text();assert src==warning.replace('def parts (p : Fin 4 → ℤ) : Parts :=','set_option linter.unusedVariables false in\ndef parts (p : Fin 4 → ℤ) : Parts :=',1)
obs=J(TASK/'observations/initial.json');assert obs['attempt_namespace_shadow']['exit_code']==1 and obs['attempt_warning']['exit_code']==0 and 'warning:' in obs['attempt_warning']['stdout'] and H(TASK/'observations/Ordinary12ConcreteSplit-warning.lean')==obs['attempt_warning']['warning_source_sha256']
# Bind source-declared 20-module historical closure to prior paired parent and
# already independently audited literal evidence, including Init's guard.
assert H(PARENT/'pair-state.json')=='04832cc18c11ad9da49d2cfc0c865baed07a18ace44d1de9d8319b150890e7dd' and H(PARENT/'author/state.json')=='b9ab036bf00296c9491ef6f06eb44aca805b51ab36f0d48e090d5620a55f6153'
assert H(SNAP/'manifest.json')=='63b846158674d41beeaa99843d92008465f8e0fe5c45bb9e1fed4b78e1a2ab48' and H(PROVIDER)=='7cbd49b6d84497c46520e908fc8c4dc105d7a0070fd1323c6c28e26bf4cf00f6' and H(LEAN)=='e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550'
prior=J(PRIOR/'receipt.json');pt=J(PRIOR/'terminal-observation.json');assert pt['exit_code']==0 and pt['receipt_sha256']==H(PRIOR/'receipt.json') and prior['status']=='PASS_INDEPENDENT_PAIRED_ARTIFACT_AUDIT' and prior['author_state_sha256']==H(PARENT/'author/state.json')
la=J(LITAUDIT/'receipt.json');lt=J(LITAUDIT/'terminal-observation.json');assert lt['audit_observed_exit_code']==0 and lt['receipt_sha256']==H(LITAUDIT/'receipt.json') and la['status']=='PASS_INDEPENDENT_ORDINARY12_LITERAL_ARTIFACT_AUDIT'
parent=J(PARENT/'author/state.json');manifest=J(SNAP/'manifest.json');provider=J(PROVIDER);assert parent['status']=='PASS' and provider['status']=='BUILT' and provider['exit_code']==0
seen=set();todo=['DiophantineConsistency.ArithmeticAdaptiveFactorUnits2011']
while todo:
 name=todo.pop()
 if name in seen or name not in manifest['sources']:continue
 seen.add(name);todo.extend(manifest['sources'][name]['imports'])
assert len(seen)==20;records={x['module']:x for x in parent['records']};tracked={};absent=set()
for name in seen:
 row=manifest['sources'][name];assert H(SNAP/row['snapshot_path'])==row['sha256']==records[name]['source_sha256'] and records[name]['exit']==0 and H(records[name]['log'])==records[name]['log_sha256']
 for path,meta in parent['outputs'][name].items():
  q=Path(path)
  if meta is None:assert not os.path.lexists(q);absent.add(path)
  else:assert q.is_file() and not q.is_symlink() and str(q.resolve())==meta['realpath'] and H(q)==meta['sha256'];tracked[path]=meta['sha256']
assert len(tracked)==20 and len(absent)==180
# Re-query exact direct imports for each freshly compiled module and verify
# its source/object hashes and successful axiom log. Saved logs are embedded
# in the pinned receipts; no unsaved external process log is assumed.
expected_deps={'Ordinary12CarrierExclusions':['ArithmeticAdaptiveFactorUnits2011'],'Ordinary12FactorSplit':['Ordinary12Residual'],'Ordinary12ComposedSplit':['Ordinary12CarrierExclusions','Ordinary12FactorSplit'],'Ordinary12Literal':['ArithmeticAdaptiveFactorMagnitude2011'],'Ordinary12Patterns':['ArithmeticAdaptiveFactorUnits2011'],'Ordinary12ConcreteSplit':['Ordinary12Literal','Ordinary12Patterns','Ordinary12FactorSplit']}
expected_reports={'Ordinary12CarrierExclusions':['first_factor_ne_negative_one','main_factor_ne_negative_one'],'Ordinary12FactorSplit':['three_factor_units','ordinary_three_factor_units'],'Ordinary12ComposedSplit':['abstract_ordinary_three_factor_units'],'Ordinary12Literal':['literal_eq_factors','raw_eval_eq_factors','product_one_of_internal_zero'],'Ordinary12Patterns':['first_ne','main_ne','ordinary_ne'],'Ordinary12ConcreteSplit':['first_eq','main_eq','ordinary_eq','literal_factor_units']}
rx=re.compile(r"^'([^']+)' depends on axioms: \[([^\]]*)\]",re.M|re.S);results={}
for label,out,receipt,pin in [('original',ORIG,TASK/'replay-receipt.json','97aa4b119f8b37a3afb8bb4cafc2c0b8e03db233eb734a67b1fe23ce8fa36572'),('independent',FRESH,FRESH_RECEIPT,'6445a4082638704c72067501a720ecc7cc571e6ae3ed88166e3b0db845306191')]:
 d=J(receipt);assert H(receipt)==pin and d['status']=='PASS_BOUNDED_ORDINARY12_CONCRETE_SPLIT' and d['graph_check_exit_code']==d['composed_replay_exit_code']==0
 comp=J(out/'composed-receipt.json');assert H(out/'composed-receipt.json')==d['composed_receipt_sha256'] and comp==d['composed_receipt'] and comp['status']=='PASS_BOUNDED_COMPOSED_MODEL_SPLIT'
 base=J(out/'composed/base-receipt.json');assert H(out/'composed/base-receipt.json')==comp['base_receipt_sha256'] and base==comp['base_receipt'] and base['status']=='PASS_BOUNDED_MODEL_RESIDUE_PROTOTYPE'
 assert base['parent_pair_sha256']==H(PARENT/'pair-state.json') and base['parent_state_sha256']==H(PARENT/'author/state.json') and base['snapshot_sha256']==H(SNAP/'manifest.json') and base['provider_sha256']==H(PROVIDER) and base['lean_sha256']==H(LEAN)
 assert set(base['project_modules'])==seen and set(base['absent_parent_paths'])==absent and {x['source'] for x in base['seed_links'].values()}==set(tracked)
 for link,meta in base['seed_links'].items():
  q=Path(link);parent_obj=Path(meta['source']);assert q==(out/'composed/base/lib'/parent_obj.relative_to(PARENT/'author/lib')) and q.is_symlink() and q.resolve()==parent_obj.resolve() and H(q)==meta['sha256']==tracked[str(parent_obj)]
 assert [x['exit_code'] for x in base['attempts']]==[1,1,0]
 attempt_results=[]
 for x in base['attempts']:
  n=x['attempt'];f=out/'composed/base'/f'attempt{n}/src/DiophantineConsistency/Ordinary12Residual.lean';original_source=(MODEL/'failed'/f'attempt{n:02}.lean') if n<3 else MODEL/'Ordinary12Residual.lean';assert H(f)==x['source_sha256']==H(original_source)
  attempt_results.append({'attempt':n,'source_sha256':H(f),'object_sha256':x['object_sha256'],'log_sha256':RAW(x['stdout']+x['stderr']),'exit_code':x['exit_code']})
  if n<3:assert 'Type mismatch' in x['stdout']+x['stderr'] and x['object_sha256'] is None
  else:assert 'sorryAx' not in x['stdout']+x['stderr'] and 'warning:' not in x['stdout']+x['stderr'] and H(out/'composed/base/attempt3/Ordinary12Residual.olean')==x['object_sha256']
 assert all(not os.path.lexists(x) for x in absent)
 for input_path,sha in d['input_sha256'].items():assert H(input_path)==sha
 modules=comp['modules']+d['modules'];assert [x['module'] for x in modules]==list(expected_deps)
 lib=out/'composed/base/lib/DiophantineConsistency';env=os.environ.copy()
 for n in ('LEAN_SRC_PATH','LEAN_SYSROOT','LD_LIBRARY_PATH','LD_PRELOAD','LD_AUDIT'):env.pop(n,None)
 env['LEAN_PATH']=str(out/'composed/base/lib')+':'+str(PACKAGE)
 residual_src=out/'composed/base/attempt3/src/DiophantineConsistency/Ordinary12Residual.lean'
 residual_deps=subprocess.run([str(LEAN),'--deps',str(residual_src)],env=env,capture_output=True,text=True,timeout=60)
 assert residual_deps.returncode==base['direct_deps_exit_code']==0 and residual_deps.stdout==base['direct_deps_stdout']
 assert set(residual_deps.stdout.splitlines())=={str(PACKAGE/'Init.olean'),str(lib/'ArithmeticAdaptiveFactorUnits2011.olean')}
 residual_dep_hashes={str(Path(q).resolve()):H(q) for q in residual_deps.stdout.splitlines()}
 mresult={}
 for row in modules:
  name=row['module'];source=out/('composed/' if name in ('Ordinary12CarrierExclusions','Ordinary12FactorSplit','Ordinary12ComposedSplit') else '')/name/'src/DiophantineConsistency'/f'{name}.lean';obj=lib/f'{name}.olean'
  original_source=(MODEL/(name+'.lean')) if name in ('Ordinary12CarrierExclusions','Ordinary12FactorSplit','Ordinary12ComposedSplit') else ((LIT/'Ordinary12Literal.lean') if name=='Ordinary12Literal' else (TASK/(name+'.lean')))
  assert row['exit_code']==0 and H(source)==row['source_sha256']==H(original_source) and H(obj)==row['object_sha256']==d['generated_objects'][name] and not obj.is_symlink()
  log=row['stdout']+row['stderr'];matches=rx.findall(log);assert [x[0] for x in matches]==['DiophantineConsistency.'+name+'.'+x for x in expected_reports[name]] and all({z.strip() for z in a.split(',')}<={'propext','Classical.choice','Quot.sound'} for _,a in matches) and 'sorryAx' not in log and 'warning:' not in log
  dep=subprocess.run([str(LEAN),'--deps',str(source)],env=env,capture_output=True,text=True,timeout=60);saved=row.get('direct_deps_stdout',row.get('deps_stdout'));assert dep.returncode==0 and dep.stdout==saved
  expected={str(PACKAGE/'Init.olean')}|{str(lib/(n+'.olean')) for n in expected_deps[name]};assert set(dep.stdout.splitlines())==expected
  dep_hashes={str(Path(q).resolve()):H(q) for q in dep.stdout.splitlines()};mresult[name]={'source_sha256':H(source),'object_sha256':H(obj),'log_sha256':RAW(log),'direct_inputs_sha256':dep_hashes}
 init=PACKAGE/'Init.olean';guard=parent['guarded_companions'][str(init)];assert H(init)==guard['sha256'] and str(init.resolve())==guard['realpath']
 results[label]={'receipt_sha256':H(receipt),'modules':mresult,'base_attempts':attempt_results,'base_residual_direct_inputs_sha256':residual_dep_hashes,'generated_objects':d['generated_objects']}
assert results['original']['generated_objects']==results['independent']['generated_objects']
assert all(results['original']['modules'][n]['source_sha256']==results['independent']['modules'][n]['source_sha256'] and results['original']['modules'][n]['object_sha256']==results['independent']['modules'][n]['object_sha256'] and results['original']['modules'][n]['log_sha256']==results['independent']['modules'][n]['log_sha256'] for n in expected_deps)
assert before=={str(p.resolve()):H(p) for p in files}
out={'status':'PASS_INDEPENDENT_ORDINARY12_CONCRETE_SPLIT_AUDIT','inputs_sha256':before,'graph_rows':100,'variables':12,'ports':4,'binding_mutations_rejected':len(mutations),'residue_controls':[64,256,256],'negative_residue_mutations':3,'parent_source_declared_closure':len(seen),'parent_output_objects':len(tracked),'results':results,'scope':'Bounded historical single-author IΣ₁-model factor split for symbolic integer ports; no compact44 checker calibration, rank recovery, free-J/95-gate transport, full package/dynamic ancestry, matched full project replay, or internal iPRA derivation.'};path=HERE/'receipt.json'
if path.exists():raise ValueError('refusing receipt overwrite')
path.write_text(json.dumps(out,sort_keys=True,indent=2)+'\n');print(out['status'],H(path))
