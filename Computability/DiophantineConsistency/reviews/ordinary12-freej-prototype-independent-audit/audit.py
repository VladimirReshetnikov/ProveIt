#!/usr/bin/env python3
"""Independent 95-row free-J graph, model theorem and bounded replay audit."""
import hashlib,itertools,json,os,re,subprocess,sys
from pathlib import Path
if not __debug__:raise RuntimeError('independent audit requires assertions enabled')
HERE=Path(__file__).resolve().parent;ROOT=HERE.parents[3];BASE=ROOT/'Computability/DiophantineConsistency';TASK=BASE/'research/ordinary12-ipra-bridge/free-j-prototype';CON=TASK.parent/'concrete-split-prototype';LIT=TASK.parent/'literal-prototype';MODEL=TASK.parent/'model-prototype';GRAPH=BASE/'con-zfc-diophantine-forms/115-synchronized-exponents/supplement/circuits/positive12_95_degree70.json';ORIG=Path('/tmp/ipra-ordinary12-freej-replay-01');FRESH=Path('/tmp/ipra-ordinary12-freej-independent-replay-02');FRESH_RECEIPT=Path('/tmp/ipra-ordinary12-freej-independent-replay-02-receipt.json');PARENT=Path('/tmp/ipra-aq29-fresh-project-pair');SNAP=Path('/tmp/ipra-aq29-fresh-source-closure-v2');PROVIDER=Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/build-all-receipt.json');PACKAGE=Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib');LEAN=Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean');PRIOR=BASE/'reviews/fresh-project-pair-independent-audit';CAUDIT=BASE/'reviews/ordinary12-concrete-split-independent-audit';MSAUDIT=BASE/'reviews/manuscript115-reconstruction-independent-audit'
H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest();J=lambda p:json.loads(Path(p).read_text());RAW=lambda s:hashlib.sha256(s.encode()).hexdigest()
files=[Path(__file__),TASK/'Ordinary12FreeJ.lean',TASK/'check_graph.py',TASK/'replay.py',TASK/'replay-receipt.json',TASK/'README.md',GRAPH,FRESH_RECEIPT,PARENT/'pair-state.json',PARENT/'author/state.json',SNAP/'manifest.json',PROVIDER,LEAN,PRIOR/'receipt.json',PRIOR/'terminal-observation.json',CAUDIT/'receipt.json',CAUDIT/'terminal-observation.json',MSAUDIT/'receipt.json',MSAUDIT/'terminal-observation.json']
before={str(p.resolve()):H(p) for p in files}
assert H(TASK/'Ordinary12FreeJ.lean')=='542bb6913f5b7e6d1ef3cd9e430fcbee20ee727966d3bfc9f2b6d71c566ef96a' and H(GRAPH)=='2348183cb8e366433f668cdcc9d77ca9c7e2d0c55b7b630bda39bd8db7506d22'
assert H(TASK/'replay-receipt.json')=='d7ac39974e9f6817709382dfe24ecb2425366096cfb2866fd0271305a5b7d1e3' and H(FRESH_RECEIPT)=='50333034445082f0cc1d7d1fcb41ae3eb76b10f2969fd531f942046b81daabe0'
for f in (TASK/'Ordinary12FreeJ.lean',TASK/'check_graph.py',TASK/'replay.py',TASK/'replay-receipt.json',TASK/'README.md'):
 b=subprocess.check_output(['git','show','f581b2a9b6:'+str(f.relative_to(ROOT))],cwd=ROOT);assert hashlib.sha256(b).hexdigest()==H(f)
g=J(GRAPH);text=(TASK/'Ordinary12FreeJ.lean').read_text();assert g['witnesses']==['J','F','alpha','t','T','X','Y','r','eta','zeta','n','gamma'] and g['fixed_numerals']==['beta','K0','MC','MF'] and g['output']=='P12'
def validate(src):
 inputs=re.findall(r'^  let (\w+) : Expr \(Fin 12\) := \.var (\d+)$',src,re.M);ports=re.findall(r'^  let (\w+) : Expr \(Fin 12\) := \.constant \(p (\d+)\)$',src,re.M)
 if inputs!=[(n,str(i)) for i,n in enumerate(g['witnesses'])] or ports!=[(n,str(i)) for i,n in enumerate(g['fixed_numerals'])]:raise ValueError('aliases')
 if src.count('  -- BEGIN LITERAL GRAPH\n')!=1 or src.count('  -- END LITERAL GRAPH\n')!=1:raise ValueError('markers')
 body=src.split('  -- BEGIN LITERAL GRAPH\n',1)[1].split('  -- END LITERAL GRAPH\n',1)[0];rows=[]
 for line in body.splitlines():
  m=re.fullmatch(r'  let (\w+) := (\w+) ([+*\-]) (\w+)',line)
  if not m:raise ValueError(('syntax',line))
  n,a,o,b=m.groups();rows.append([n,o,int(a) if a.isdecimal() else a,int(b) if b.isdecimal() else b])
 if rows!=g['source'] or len(rows)!=95:raise ValueError('rows')
 if src.count('  ⟨g94,g95,g97,P12,qm,Z,g41,U,a,c,Dstar,polarA,den,polarT,polarCy⟩\n')!=1:raise ValueError('core tuple')
 return rows
rows=validate(text);index={x[0]:x for x in rows};assert len(index)==95
for row in (['qm','*','J','beta'],['g94','+',1,'A0'],['g95','+',1,'A1'],['g97','+',1,'N'],['g96','*','g94','g95'],['g98','*','g96','g97'],['P12','-','g98',1]):assert index[row[0]]==row
known=set(g['witnesses']+g['fixed_numerals'])
for name,op,a,b in rows:assert name not in known and all(type(x) is int or x in known for x in (a,b));known.add(name)
assert 'variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]' in text
statement=' '.join(text.split('theorem literal_factor_units ',1)[1].split(':= by',1)[0].split())
assert statement==('(p : Fin 4 → ℤ) (v : Fin 12 → V) (h : InternalZero (literal p) v) : '
 '(pairEval (core p).first v).1 = (pairEval (core p).first v).2 + 1 ∧ '
 '(pairEval (core p).main v).1 = (pairEval (core p).main v).2 + 1 ∧ '
 '(pairEval (core p).ordinary v).1 = (pairEval (core p).ordinary v).2 + 1')
for x in ('apply three_factor_units (product_one_of_internal_zero p v h)','exact first_ne _ _ _ v','exact main_ne _ _ _ _ v','exact polarized_ne _ _ _ _ v','1+(a*a+((4*(d*t))*c))'):assert x in text
mutations=[('let qm := J * beta','let qm := J + beta'),('let J : Expr (Fin 12) := .var 0','let J : Expr (Fin 12) := .var 1'),('let K0 : Expr (Fin 12) := .constant (p 1)','let K0 : Expr (Fin 12) := .constant (p 0)'),('⟨g94,g95,g97,P12','⟨g94,g95,N,P12'),('let polarCorrection := polar4DT * polarCy','let polarCorrection := polar4DT + polarCy'),('let P12 := g98 - 1','let P12 := g98 + 1')]
for old,new in mutations:
 assert text.count(old)==1
 try:validate(text.replace(old,new,1))
 except ValueError:pass
 else:raise AssertionError(('mutation accepted',old))
assert all((1+a*a+4*d*t*c)%4!=3 for a,d,t,c in itertools.product(range(4),repeat=4))
assert any((1+a*a+d*t*c)%4==3 for a,d,t,c in itertools.product(range(4),repeat=4))
check=subprocess.run([sys.executable,str(TASK/'check_graph.py')],capture_output=True,text=True,timeout=60);assert check.returncode==0 and check.stdout.strip()=='PASS_FREE_J_GRAPH 95 rows 12 free variables 4 ports 4 mutations rejected'
checkopt=subprocess.run([sys.executable,'-O',str(TASK/'check_graph.py')],capture_output=True,text=True,timeout=30);assert checkopt.returncode!=0 and 'checks require Python assertions enabled' in checkopt.stderr
ca=J(CAUDIT/'receipt.json');ct=J(CAUDIT/'terminal-observation.json');assert H(CAUDIT/'receipt.json')=='d89fb87aec30f7986cf3fa25f265fd2d9e1b731bbde0402319cad8a057297b60' and ct['audit_observed_exit_code']==0 and ct['receipt_sha256']==H(CAUDIT/'receipt.json') and ca['status']=='PASS_INDEPENDENT_ORDINARY12_CONCRETE_SPLIT_AUDIT'
ma=J(MSAUDIT/'receipt.json');mt=J(MSAUDIT/'terminal-observation.json');assert mt['observed_exit_code']==0 and mt['receipt_sha256']==H(MSAUDIT/'receipt.json') and ma['status']=='PASS_INDEPENDENT_MANUSCRIPT115_RECONSTRUCTION_REVIEW' and ma['child_gates']==95 and ma['degree_upper']==70
assert H(PARENT/'pair-state.json')=='04832cc18c11ad9da49d2cfc0c865baed07a18ace44d1de9d8319b150890e7dd' and H(PARENT/'author/state.json')=='b9ab036bf00296c9491ef6f06eb44aca805b51ab36f0d48e090d5620a55f6153' and H(SNAP/'manifest.json')=='63b846158674d41beeaa99843d92008465f8e0fe5c45bb9e1fed4b78e1a2ab48'
assert H(PROVIDER)=='7cbd49b6d84497c46520e908fc8c4dc105d7a0070fd1323c6c28e26bf4cf00f6' and H(LEAN)=='e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550'
parent=J(PARENT/'author/state.json');manifest=J(SNAP/'manifest.json');pr=J(PRIOR/'receipt.json');pt=J(PRIOR/'terminal-observation.json');assert pt['exit_code']==0 and pt['receipt_sha256']==H(PRIOR/'receipt.json') and pr['author_state_sha256']==H(PARENT/'author/state.json')
seen=set();todo=['DiophantineConsistency.ArithmeticAdaptiveFactorUnits2011']
while todo:
 n=todo.pop()
 if n in seen or n not in manifest['sources']:continue
 seen.add(n);todo.extend(manifest['sources'][n]['imports'])
assert len(seen)==20;records={x['module']:x for x in parent['records']};tracked={};absent=set()
for n in seen:
 row=manifest['sources'][n];assert H(SNAP/row['snapshot_path'])==row['sha256']==records[n]['source_sha256'] and records[n]['exit']==0 and H(records[n]['log'])==records[n]['log_sha256']
 for path,meta in parent['outputs'][n].items():
  q=Path(path)
  if meta is None:assert not os.path.lexists(q);absent.add(path)
  else:assert q.is_file() and not q.is_symlink() and str(q.resolve())==meta['realpath'] and H(q)==meta['sha256'];tracked[path]=meta['sha256']
assert len(tracked)==20 and len(absent)==180
rx=re.compile(r"^'([^']+)' depends on axioms: \[([^\]]*)\]",re.M|re.S);names=['polarized_ne','first_eq','main_eq','ordinary_eq','literal_eq_factors','product_one_of_internal_zero','literal_factor_units'];results={}
for label,out,receipt,pin in [('original',ORIG,TASK/'replay-receipt.json','d7ac39974e9f6817709382dfe24ecb2425366096cfb2866fd0271305a5b7d1e3'),('independent',FRESH,FRESH_RECEIPT,'50333034445082f0cc1d7d1fcb41ae3eb76b10f2969fd531f942046b81daabe0')]:
 d=J(receipt);assert H(receipt)==pin and d['status']=='PASS_BOUNDED_FREE_J_95_FACTOR_SPLIT' and d['graph_check_exit_code']==d['inner_exit_code']==d['lean_exit_code']==d['deps_exit_code']==0
 inner=J(out/'concrete-receipt.json');assert H(out/'concrete-receipt.json')==d['inner_receipt_sha256'] and inner==d['inner_receipt'] and inner['status']=='PASS_BOUNDED_ORDINARY12_CONCRETE_SPLIT'
 comp=J(out/'concrete/composed-receipt.json');assert H(out/'concrete/composed-receipt.json')==inner['composed_receipt_sha256'] and comp==inner['composed_receipt'] and comp['status']=='PASS_BOUNDED_COMPOSED_MODEL_SPLIT'
 base=J(out/'concrete/composed/base-receipt.json');assert H(out/'concrete/composed/base-receipt.json')==comp['base_receipt_sha256'] and base==comp['base_receipt'] and base['status']=='PASS_BOUNDED_MODEL_RESIDUE_PROTOTYPE'
 assert base['parent_pair_sha256']==H(PARENT/'pair-state.json') and base['parent_state_sha256']==H(PARENT/'author/state.json') and base['snapshot_sha256']==H(SNAP/'manifest.json') and base['provider_sha256']==H(PROVIDER) and base['lean_sha256']==H(LEAN)
 assert set(base['project_modules'])==seen and set(base['absent_parent_paths'])==absent and {x['source'] for x in base['seed_links'].values()}==set(tracked)
 for link,meta in base['seed_links'].items():
  q=Path(link);source=Path(meta['source']);assert q==(out/'concrete/composed/base/lib'/source.relative_to(PARENT/'author/lib')) and q.is_symlink() and q.resolve()==source.resolve() and H(q)==meta['sha256']==tracked[str(source)]
 assert all(not os.path.lexists(x) for x in absent) and [x['exit_code'] for x in base['attempts']]==[1,1,0]
 lib=out/'concrete/composed/base/lib/DiophantineConsistency'
 for name,sha in inner['generated_objects'].items():assert H(lib/(name+'.olean'))==sha==ca['results']['original']['generated_objects'][name]
 expected_inner={'Ordinary12CarrierExclusions':['ArithmeticAdaptiveFactorUnits2011'],'Ordinary12FactorSplit':['Ordinary12Residual'],'Ordinary12ComposedSplit':['Ordinary12CarrierExclusions','Ordinary12FactorSplit'],'Ordinary12Literal':['ArithmeticAdaptiveFactorMagnitude2011'],'Ordinary12Patterns':['ArithmeticAdaptiveFactorUnits2011'],'Ordinary12ConcreteSplit':['Ordinary12Literal','Ordinary12Patterns','Ordinary12FactorSplit']}
 compiled=comp['modules']+inner['modules'];assert [r['module'] for r in compiled]==list(expected_inner)
 inner_env=os.environ.copy()
 for n in ('LEAN_SRC_PATH','LEAN_SYSROOT','LD_LIBRARY_PATH','LD_PRELOAD','LD_AUDIT'):inner_env.pop(n,None)
 inner_env['LEAN_PATH']=str(out/'concrete/composed/base/lib')+':'+str(PACKAGE)
 inner_results={}
 for row in compiled:
  name=row['module'];source=out/'concrete'/('composed/' if name in ('Ordinary12CarrierExclusions','Ordinary12FactorSplit','Ordinary12ComposedSplit') else '')/name/'src/DiophantineConsistency'/f'{name}.lean';obj0=lib/f'{name}.olean';known=ca['results']['original']['modules'][name]
  log0=row['stdout']+row['stderr'];assert row['exit_code']==0 and H(source)==row['source_sha256']==known['source_sha256'] and H(obj0)==row['object_sha256']==known['object_sha256'] and RAW(log0)==known['log_sha256'] and 'sorryAx' not in log0 and 'warning:' not in log0
  dep0=subprocess.run([str(LEAN),'--deps',str(source)],env=inner_env,capture_output=True,text=True,timeout=60);saved=row.get('direct_deps_stdout',row.get('deps_stdout'));assert dep0.returncode==0 and dep0.stdout==saved
  assert set(dep0.stdout.splitlines())==({str(PACKAGE/'Init.olean')}|{str(lib/(n+'.olean')) for n in expected_inner[name]})
  inner_results[name]={'source_sha256':H(source),'object_sha256':H(obj0),'log_sha256':RAW(log0),'direct_inputs_sha256':{str(Path(q).resolve()):H(q) for q in dep0.stdout.splitlines()}}
 for x in base['attempts']:
  n=x['attempt'];source=out/'concrete/composed/base'/f'attempt{n}/src/DiophantineConsistency/Ordinary12Residual.lean';original=(MODEL/'failed'/f'attempt{n:02}.lean') if n<3 else MODEL/'Ordinary12Residual.lean';assert H(source)==x['source_sha256']==H(original)
  if n<3:assert 'Type mismatch' in x['stdout']+x['stderr'] and x['object_sha256'] is None
  else:assert 'sorryAx' not in x['stdout']+x['stderr'] and H(out/'concrete/composed/base/attempt3/Ordinary12Residual.olean')==x['object_sha256']
 residual=out/'concrete/composed/base/attempt3/src/DiophantineConsistency/Ordinary12Residual.lean';rd=subprocess.run([str(LEAN),'--deps',str(residual)],env=inner_env,capture_output=True,text=True,timeout=60);assert rd.returncode==base['direct_deps_exit_code']==0 and rd.stdout==base['direct_deps_stdout'] and set(rd.stdout.splitlines())=={str(PACKAGE/'Init.olean'),str(lib/'ArithmeticAdaptiveFactorUnits2011.olean')}
 src=out/'src/DiophantineConsistency/Ordinary12FreeJ.lean';obj=lib/'Ordinary12FreeJ.olean';assert H(src)==H(TASK/'Ordinary12FreeJ.lean') and H(obj)==d['object_sha256']=='140165359b2af75052e1179b5dbb4f4450d1f6c37417c017bc354ae08eb4a7e9' and not obj.is_symlink()
 log=d['lean_stdout']+d['lean_stderr'];matches=rx.findall(log);assert [n for n,_ in matches]==['DiophantineConsistency.Ordinary12FreeJ.'+n for n in names] and all({x.strip() for x in v.split(',')}<={'propext','Classical.choice','Quot.sound'} for _,v in matches) and 'sorryAx' not in log and 'warning:' not in log
 env=os.environ.copy()
 for n in ('LEAN_SRC_PATH','LEAN_SYSROOT','LD_LIBRARY_PATH','LD_PRELOAD','LD_AUDIT'):env.pop(n,None)
 env['LEAN_PATH']=str(out/'concrete/composed/base/lib')+':'+str(PACKAGE)
 deps=subprocess.run([str(LEAN),'--deps',str(src)],env=env,capture_output=True,text=True,timeout=60);assert deps.returncode==0 and deps.stdout==d['deps_stdout']
 expected={str(PACKAGE/'Init.olean'),str(lib/'Ordinary12Patterns.olean'),str(lib/'Ordinary12FactorSplit.olean')};assert set(deps.stdout.splitlines())==expected
 assert H(PACKAGE/'Init.olean')==parent['guarded_companions'][str(PACKAGE/'Init.olean')]['sha256']
 for path,sha in d['inputs_sha256'].items():assert H(path)==sha
 results[label]={'receipt_sha256':H(receipt),'inner_receipt_sha256':H(out/'concrete-receipt.json'),'source_sha256':H(src),'object_sha256':H(obj),'log_sha256':RAW(log),'direct_inputs_sha256':{str(Path(q).resolve()):H(q) for q in deps.stdout.splitlines()},'generated_objects':inner['generated_objects'],'inner_modules':inner_results,'residual_direct_inputs_sha256':{str(Path(q).resolve()):H(q) for q in rd.stdout.splitlines()}}
assert results['original']['object_sha256']==results['independent']['object_sha256'] and results['original']['log_sha256']==results['independent']['log_sha256'] and results['original']['generated_objects']==results['independent']['generated_objects']
assert before=={str(p.resolve()):H(p) for p in files}
out={'status':'PASS_INDEPENDENT_ORDINARY12_FREE_J_ARTIFACT_AUDIT','inputs_sha256':before,'graph_rows':95,'variables':12,'ports':4,'mutations_rejected':len(mutations),'polarized_residue_cases':256,'mutated_polarized_counterexample':True,'parent_source_declared_closure':len(seen),'parent_output_objects':len(tracked),'results':results,'scope':'Bounded historical single-author IΣ₁-model factor split for free J and symbolic integer ports; no compact44 checker calibration, rank/congruence recovery, full package/dynamic ancestry, matched full project replay, or internal iPRA derivation.'};path=HERE/'receipt.json'
if path.exists():raise ValueError('refusing receipt overwrite')
path.write_text(json.dumps(out,sort_keys=True,indent=2)+'\n');print(out['status'],H(path))
