#!/usr/bin/env python3
"""Independent review of the literal graph and two bounded replay artifacts."""
import copy,hashlib,json,os,re,subprocess,sys,time
from pathlib import Path
if not __debug__:raise RuntimeError('independent audit requires assertions enabled')
HERE=Path(__file__).resolve().parent;ROOT=HERE.parents[3];BASE=ROOT/'Computability/DiophantineConsistency';TASK=BASE/'research/ordinary12-ipra-bridge/literal-prototype';MODEL=TASK.parent/'model-prototype';GRAPH=BASE/'research/ordinary-unit-products/p12_ordinary_degree70.json';ORIG=Path('/tmp/ipra-ordinary12-literal-replay-01');FRESH=Path('/tmp/ipra-ordinary12-literal-independent-replay-02');FRESH_RECEIPT=Path('/tmp/ipra-ordinary12-literal-independent-replay-02-receipt.json');PARENT=Path('/tmp/ipra-aq29-fresh-project-pair');SNAP=Path('/tmp/ipra-aq29-fresh-source-closure-v2');PROVIDER=Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/build-all-receipt.json');PACKAGE=Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib');LEAN=Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean');PRIOR=BASE/'reviews/fresh-project-pair-independent-audit'
H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest();J=lambda p:json.loads(Path(p).read_text());RAW=lambda s:hashlib.sha256(s.encode()).hexdigest()
files=[Path(__file__),TASK/'Ordinary12Literal.lean',TASK/'check_literal.py',TASK/'replay.py',TASK/'replay-receipt.json',TASK/'README.md',MODEL/'replay.py',GRAPH,FRESH_RECEIPT,ORIG/'base-receipt.json',FRESH/'base-receipt.json',PARENT/'pair-state.json',PARENT/'author/state.json',SNAP/'manifest.json',PROVIDER,LEAN,PRIOR/'receipt.json',PRIOR/'terminal-observation.json']
before={str(p.resolve()):H(p) for p in files}
assert H(TASK/'Ordinary12Literal.lean')=='23a22eebc33d262e1b4c134c6072e808c002aac31a627def951bc753d3e96709'
assert H(GRAPH)=='444c25b68fbfee600ae174cb5bad1931897a55ffe2f9570fd22f3281f6e97010'
assert H(TASK/'replay-receipt.json')=='872730f7137015c6fb35b053b27ba634c630c4d1974058e925c1bfb45038c763' and H(FRESH_RECEIPT)=='d8aaf21177c04fa98cd519d4f362d59da8c4bb75c6625acd5742c324daf2dc9d'
for f in (TASK/'Ordinary12Literal.lean',TASK/'check_literal.py',TASK/'replay.py',TASK/'replay-receipt.json',TASK/'README.md'):
 blob=subprocess.check_output(['git','show','a5ccd8d397:'+str(f.relative_to(ROOT))],cwd=ROOT);assert hashlib.sha256(blob).hexdigest()==H(f)
g=J(GRAPH);text=(TASK/'Ordinary12Literal.lean').read_text();assert len(g['witnesses'])==12 and g['fixed_numerals']==['beta','K0','MC','MF'] and g['output']=='P12'
# Parse the Lean file independently of the author's graph validator.
def validate(src):
 inputs=re.findall(r'^  let (\w+) : Expr \(Fin 12\) := \.var (\d+)$',src,re.M)
 ports=re.findall(r'^  let (\w+) : Expr \(Fin 12\) := \.constant \(p (\d+)\)$',src,re.M)
 if inputs!=[(n,str(i)) for i,n in enumerate(g['witnesses'])] or ports!=[(n,str(i)) for i,n in enumerate(g['fixed_numerals'])]:raise ValueError('aliases')
 if src.count('  -- BEGIN LITERAL GRAPH\n')!=1 or src.count('  -- END LITERAL GRAPH\n')!=1:raise ValueError('markers')
 body=src.split('  -- BEGIN LITERAL GRAPH\n',1)[1].split('  -- END LITERAL GRAPH\n',1)[0];rows=[]
 for line in body.splitlines():
  m=re.fullmatch(r'  let (\w+) := (\w+) ([+*\-]) (\w+)',line)
  if not m:raise ValueError(('syntax',line))
  name,a,op,b=m.groups();rows.append([name,op,int(a) if a.isdecimal() else a,int(b) if b.isdecimal() else b])
 if rows!=g['source'] or len(rows)!=100:raise ValueError('rows')
 if src.count('  ⟨g94, g95, g97, P12⟩\n')!=1:raise ValueError('factors')
 return rows
rows=validate(text);idx={x[0]:x for x in rows};assert len(idx)==100
for row in (['g94','+',1,'A0'],['g95','+',1,'A1'],['g97','+',1,'N'],['g96','*','g94','g95'],['g98','*','g96','g97'],['P12','-','g98',1]):assert idx[row[0]]==row
known=set(g['witnesses']+g['fixed_numerals'])
for name,op,a,b in rows:
 assert name not in known and all(type(x) is int or x in known for x in (a,b));known.add(name)
# Exact stated theorem interfaces and assumptions, not merely axiom labels.
for snippet in (
 'theorem literal_eq_factors (p : Fin 4 → ℤ) :\n    literal p = (core p).first * (core p).main * (core p).ordinary - 1 := by',
 'theorem raw_eval_eq_factors (p : Fin 4 → ℤ) (v : Fin 12 → ℤ) :\n    (literal p).eval v = (core p).first.eval v * (core p).main.eval v *\n      (core p).ordinary.eval v - 1 := by',
 'variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]',
 'theorem product_one_of_internal_zero (p : Fin 4 → ℤ) (v : Fin 12 → V)\n    (hz : InternalZero (literal p) v) :\n    Equivalent (multiply (multiply (pairEval (core p).first v)\n      (pairEval (core p).main v)) (pairEval (core p).ordinary v)) (natural (1:V)) := by'):
 assert snippet in text
mutations=[('  let g0 := 6 * j\n','  let g0 := 6 + j\n'),('  let j : Expr (Fin 12) := .var 0\n','  let j : Expr (Fin 12) := .var 1\n'),('  let beta : Expr (Fin 12) := .constant (p 0)\n','  let beta : Expr (Fin 12) := .constant (p 1)\n'),('  ⟨g94, g95, g97, P12⟩\n','  ⟨g95, g95, g97, P12⟩\n'),('  let g97 := 1 + N\n','  let g97 := 1 - N\n'),('  let P12 := g98 - 1\n','  let P12 := g98 + 1\n')]
for old,new in mutations:
 assert text.count(old)==1
 try:validate(text.replace(old,new,1))
 except ValueError:pass
 else:raise AssertionError(('mutation accepted',old))
check=subprocess.run([sys.executable,str(TASK/'check_literal.py')],capture_output=True,text=True,timeout=60);assert check.returncode==0 and check.stdout.strip()=='PASS_ORDINARY12_LITERAL_GRAPH 100 rows 12 inputs 4 ports 4 mutations rejected'
checkopt=subprocess.run([sys.executable,'-O',str(TASK/'check_literal.py')],capture_output=True,text=True,timeout=30);assert checkopt.returncode!=0 and 'literal checks require Python assertions enabled' in checkopt.stderr
# Pin the author and peer parent through the already independent matched audit.
assert H(PARENT/'pair-state.json')=='04832cc18c11ad9da49d2cfc0c865baed07a18ace44d1de9d8319b150890e7dd'
assert H(PARENT/'author/state.json')=='b9ab036bf00296c9491ef6f06eb44aca805b51ab36f0d48e090d5620a55f6153'
assert H(SNAP/'manifest.json')=='63b846158674d41beeaa99843d92008465f8e0fe5c45bb9e1fed4b78e1a2ab48'
assert H(PROVIDER)=='7cbd49b6d84497c46520e908fc8c4dc105d7a0070fd1323c6c28e26bf4cf00f6' and H(LEAN)=='e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550'
prior=J(PRIOR/'receipt.json');terminal=J(PRIOR/'terminal-observation.json');assert terminal['exit_code']==0 and terminal['receipt_sha256']==H(PRIOR/'receipt.json') and prior['status']=='PASS_INDEPENDENT_PAIRED_ARTIFACT_AUDIT' and prior['pair_state_sha256']==H(PARENT/'pair-state.json') and prior['author_state_sha256']==H(PARENT/'author/state.json')
parent=J(PARENT/'author/state.json');manifest=J(SNAP/'manifest.json');provider=J(PROVIDER);assert parent['status']=='PASS' and provider['status']=='BUILT' and provider['exit_code']==0
# Recompute the source-declared closure and bind each source/object/log to
# the already audited parent, including all expected absent companions.
seen=set();todo=['DiophantineConsistency.ArithmeticAdaptiveFactorUnits2011']
while todo:
 name=todo.pop()
 if name in seen or name not in manifest['sources']:continue
 seen.add(name);todo.extend(manifest['sources'][name]['imports'])
assert len(seen)==20;records={r['module']:r for r in parent['records']};tracked={}
for name in seen:
 row=manifest['sources'][name];source=SNAP/row['snapshot_path'];assert H(source)==row['sha256']==records[name]['source_sha256'] and records[name]['exit']==0 and H(records[name]['log'])==records[name]['log_sha256']
 for path,meta in parent['outputs'][name].items():
  q=Path(path)
  if meta is None:assert not os.path.lexists(q)
  else:assert q.is_file() and not q.is_symlink() and str(q.resolve())==meta['realpath'] and H(q)==meta['sha256'];tracked[path]=meta['sha256']
assert len(tracked)==20
expected_absent={path for name in seen for path,meta in parent['outputs'][name].items() if meta is None};assert len(expected_absent)==180
# Independently query Lean direct dependencies of both immutable compiled
# literal sources, hash the input objects and compare recorded process logs.
expected_names=['DiophantineConsistency.Ordinary12Literal.literal_eq_factors','DiophantineConsistency.Ordinary12Literal.raw_eval_eq_factors','DiophantineConsistency.Ordinary12Literal.product_one_of_internal_zero']
regex=re.compile(r"^'([^']+)' depends on axioms: \[([^\]]*)\]",re.M|re.S)
results={}
for label,out,receipt,receipt_hash in [('original',ORIG,TASK/'replay-receipt.json','872730f7137015c6fb35b053b27ba634c630c4d1974058e925c1bfb45038c763'),('independent',FRESH,FRESH_RECEIPT,'d8aaf21177c04fa98cd519d4f362d59da8c4bb75c6625acd5742c324daf2dc9d')]:
 d=J(receipt);assert H(receipt)==receipt_hash and d['status']=='PASS_BOUNDED_ORDINARY12_LITERAL_IDENTITY' and d['lean_exit_code']==d['graph_check_exit_code']==d['base_replay_exit_code']==d['direct_deps_exit_code']==0
 base=J(out/'base-receipt.json');assert H(out/'base-receipt.json')==d['base_receipt_sha256'] and base==d['base_receipt'] and base['status']=='PASS_BOUNDED_MODEL_RESIDUE_PROTOTYPE'
 assert base['parent_pair_sha256']==H(PARENT/'pair-state.json') and base['parent_state_sha256']==H(PARENT/'author/state.json') and base['snapshot_sha256']==H(SNAP/'manifest.json') and base['provider_sha256']==H(PROVIDER) and base['lean_sha256']==H(LEAN)
 assert set(base['project_modules'])==seen and len(base['seed_links'])==20 and set(base['absent_parent_paths'])==expected_absent and base['replay_sha256']==H(MODEL/'replay.py')
 assert {meta['source'] for meta in base['seed_links'].values()}==set(tracked)
 for input_path,input_sha in d['inputs_sha256'].items():assert H(input_path)==input_sha
 for link,meta in base['seed_links'].items():
  q=Path(link);source=Path(meta['source']);assert q==(out/'base/lib'/source.relative_to(PARENT/'author/lib')) and q.is_symlink() and q.resolve()==source.resolve() and str(source) in tracked and H(q)==meta['sha256']==tracked[str(source)]
 assert all(not os.path.lexists(p) for p in base['absent_parent_paths'])
 attempts=base['attempts'];assert [x['exit_code'] for x in attempts]==[1,1,0]
 for x in attempts:
  n=x['attempt'];src=out/'base'/f'attempt{n}/src/DiophantineConsistency/Ordinary12Residual.lean';obj=out/'base'/f'attempt{n}/Ordinary12Residual.olean';model_source=(MODEL/'failed'/f'attempt{n:02}.lean') if n<3 else MODEL/'Ordinary12Residual.lean';assert H(src)==x['source_sha256']==H(model_source)
  if n<3:assert x['object_sha256'] is None and not obj.exists() and 'Type mismatch' in x['stdout']+x['stderr']
  else:assert H(obj)==x['object_sha256']=='853bd3e797a9114752e57a94759b23704f4761f478624df14f6f118b72839242' and 'sorryAx' not in x['stdout']+x['stderr']
 src=out/'literal/src/DiophantineConsistency/Ordinary12Literal.lean';obj=out/'literal/Ordinary12Literal.olean';assert H(src)==H(TASK/'Ordinary12Literal.lean') and H(obj)==d['object_sha256']=='4a54755cec19d9c6c34b9906b6b9763c730e7e6cf37cfc516f99c2168a9192f8' and not obj.is_symlink()
 logs=d['lean_stdout']+d['lean_stderr'];reports=regex.findall(logs);assert [x[0] for x in reports]==expected_names and all({v.strip() for v in x[1].split(',')} <= {'propext','Classical.choice','Quot.sound'} for x in reports) and 'sorryAx' not in logs and 'warning:' not in logs
 env=os.environ.copy()
 for n in ('LEAN_SRC_PATH','LEAN_SYSROOT','LD_LIBRARY_PATH','LD_PRELOAD','LD_AUDIT'):env.pop(n,None)
 env['LEAN_PATH']=str(out/'base/lib')+':'+str(PACKAGE)
 deps=subprocess.run([str(LEAN),'--deps',str(src)],env=env,capture_output=True,text=True,timeout=60);assert deps.returncode==0 and deps.stdout==d['direct_deps_stdout']
 dep_lines=deps.stdout.splitlines();expected=[str(PACKAGE/'Init.olean'),str(PACKAGE/'Init.olean'),str(out/'base/lib/DiophantineConsistency/ArithmeticAdaptiveFactorMagnitude2011.olean')];assert dep_lines==expected
 magnitude=Path(dep_lines[-1]);assert magnitude.is_symlink() and str(magnitude.resolve()) in tracked and H(magnitude)==tracked[str(magnitude.resolve())]
 init=Path(dep_lines[0]);assert init.is_file() and init.resolve()==LEAN.parent.parent/'lib/lean/Init.olean'
 init_guard=parent['guarded_companions'][str(init)];assert init_guard['realpath']==str(init.resolve()) and init_guard['sha256']==H(init)
 results[label]={'receipt_sha256':H(receipt),'base_receipt_sha256':H(out/'base-receipt.json'),'source_sha256':H(src),'object_sha256':H(obj),'lean_log_sha256':RAW(logs),'direct_deps_stdout_sha256':RAW(deps.stdout),'init_sha256':H(init),'magnitude_sha256':H(magnitude),'attempt_exit_codes':[x['exit_code'] for x in attempts]}
assert results['original']['source_sha256']==results['independent']['source_sha256'] and results['original']['object_sha256']==results['independent']['object_sha256'] and results['original']['lean_log_sha256']==results['independent']['lean_log_sha256']
assert before=={str(p.resolve()):H(p) for p in files}
out={'status':'PASS_INDEPENDENT_ORDINARY12_LITERAL_ARTIFACT_AUDIT','inputs_sha256':before,'graph_rows':100,'variables':12,'ports':4,'mutations_rejected':len(mutations),'parent_source_declared_closure':len(seen),'parent_output_objects':len(tracked),'results':results,'original_checker_exit':check.returncode,'original_checker_optimized_exit':checkopt.returncode,'scope':'Bounded historical source-declared overlay; no concrete factor split, compact44 checker calibration, rank recovery, full package/dynamic ancestry, matched full project replay, or iPRA derivation.'};path=HERE/'receipt.json'
if path.exists():raise ValueError('refusing receipt overwrite')
path.write_text(json.dumps(out,sort_keys=True,indent=2)+'\n');print(out['status'],H(path))
