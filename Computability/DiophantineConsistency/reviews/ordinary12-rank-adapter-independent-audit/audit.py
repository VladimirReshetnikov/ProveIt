#!/usr/bin/env python3
"""Independent artifact and explicit-hypothesis audit of the rank adapter."""
import hashlib,json,os,re,subprocess,sys
from pathlib import Path
if not __debug__:raise RuntimeError('independent audit requires assertions enabled')
HERE=Path(__file__).resolve().parent;ROOT=HERE.parents[3];BASE=ROOT/'Computability/DiophantineConsistency';TASK=BASE/'research/ordinary12-ipra-bridge/rank-adapter-prototype';FREEJ=TASK.parent/'free-j-prototype';ORIG=Path('/tmp/ipra-ordinary12-rank-replay-01');FRESH=Path('/tmp/ipra-ordinary12-rank-adapter-independent-replay-02');FRESH_RECEIPT=Path('/tmp/ipra-ordinary12-rank-adapter-independent-replay-02-receipt.json');PARENT=Path('/tmp/ipra-aq29-fresh-project-pair');SNAP=Path('/tmp/ipra-aq29-fresh-source-closure-v2');PROVIDER=Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/build-all-receipt.json');PACKAGE=Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib');LEAN=Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean');PRIOR=BASE/'reviews/fresh-project-pair-independent-audit';FAUDIT=BASE/'reviews/ordinary12-freej-prototype-independent-audit'
H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest();J=lambda p:json.loads(Path(p).read_text());RAW=lambda s:hashlib.sha256(s.encode()).hexdigest()
files=[Path(__file__),TASK/'Ordinary12RankAdapter.lean',TASK/'replay.py',TASK/'replay-receipt.json',TASK/'README.md',FREEJ/'Ordinary12FreeJ.lean',FREEJ/'replay.py',FRESH_RECEIPT,PARENT/'pair-state.json',PARENT/'author/state.json',SNAP/'manifest.json',PROVIDER,LEAN,PRIOR/'receipt.json',PRIOR/'terminal-observation.json',FAUDIT/'receipt.json',FAUDIT/'terminal-observation.json']
before={str(p.resolve()):H(p) for p in files}
assert H(TASK/'Ordinary12RankAdapter.lean')=='0db8060c5c0a130a66944775f21c1cc7ff324c5737afc712e47c0af50df20ea5' and H(TASK/'replay-receipt.json')=='955f79233a43e2500aa2f477a51bc097ad419604b2306e908ff9fd54236d2a06' and H(FRESH_RECEIPT)=='af62476a18442067e088d3d611937e12b18e26815a300b82684c8de1db929348'
for f in (TASK/'Ordinary12RankAdapter.lean',TASK/'replay.py',TASK/'replay-receipt.json',TASK/'README.md'):
 assert hashlib.sha256(subprocess.check_output(['git','show','80695899da:'+str(f.relative_to(ROOT))],cwd=ROOT)).hexdigest()==H(f)
source=(TASK/'Ordinary12RankAdapter.lean').read_text();assert 'variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]' in source
def statement(s,name):
 x=s.split('theorem '+name,1)
 if len(x)!=2:raise ValueError('missing theorem')
 return ' '.join(x[1].split(':= by',1)[0].split())
def validate(s):
 if statement(s,'conditional_compact44_cancellations') != ('(q Y X t R J : V) (hqpos : 0 < q) (hY : q^3 ∣ Y) (hH : q^5 ∣ (3+4*Y*(X+1))*t) (hq : q = (Exp.exp (590069:V)-1)*J+1) (h3 : q ∣ 3*Exp.exp R) : q^4 ∣ t ∧ q ∣ Exp.exp R'):raise ValueError('cancellation statement')
 if statement(s,'conditional_freeJ_split_and_cancellations') != ('(p : Fin 4 → ℤ) (v : Fin 12 → V) (hzero : InternalZero (literal p) v) (q Y X t R J : V) (hqpos : 0 < q) (hY : q^3 ∣ Y) (hH : q^5 ∣ (3+4*Y*(X+1))*t) (hq : q = (Exp.exp (590069:V)-1)*J+1) (h3 : q ∣ 3*Exp.exp R) : ((pairEval (core p).first v).1 = (pairEval (core p).first v).2 + 1 ∧ (pairEval (core p).main v).1 = (pairEval (core p).main v).2 + 1 ∧ (pairEval (core p).ordinary v).1 = (pairEval (core p).ordinary v).2 + 1) ∧ q^4 ∣ t ∧ q ∣ Exp.exp R'):raise ValueError('combined statement')
 for x in ('exact cancel_factor_three q Y X t hqpos hY hH','exact cancel_three (590069:V) R q J (by norm_num) hq h3','literal_factor_units p v hzero','conditional_compact44_cancellations q Y X t R J hqpos hY hH hq h3'):
  if s.count(x)!=1:raise ValueError(('branch mismatch',x))
validate(source)
mutations=[('hY : q^3 ∣ Y','hY : q^2 ∣ Y'),('hH : q^5 ∣','hH : q^4 ∣'),('590069:V','590068:V'),('exact cancel_factor_three q Y X t hqpos hY hH','exact cancel_factor_three q Y X t hqpos hY h3'),('h3 : q ∣ 3*Exp.exp R','h3 : q ∣ Exp.exp R')]
for old,new in mutations:
 assert old in source
 try:validate(source.replace(old,new,1))
 except ValueError:pass
 else:raise AssertionError(('mutation accepted',old))
# Numerical sanity witnesses confirm the first cancellation is not assuming
# 3 ∤ q and the second needs its explicit divisibility premise.
q,Y,X,t=3,27,0,81;assert q>0 and Y%q**3==0 and ((3+4*Y*(X+1))*t)%q**5==0 and t%q**4==0 and q%3==0
# Bind prior independent free-J review and matched historical parent.
fa=J(FAUDIT/'receipt.json');ft=J(FAUDIT/'terminal-observation.json');assert H(FAUDIT/'receipt.json')=='9fa181917cfd6246c4dc8f305d8ced81cc1c6baf628adc97d6e78e43ec42c706' and ft['audit_observed_exit_code']==0 and ft['receipt_sha256']==H(FAUDIT/'receipt.json') and fa['status']=='PASS_INDEPENDENT_ORDINARY12_FREE_J_ARTIFACT_AUDIT'
assert H(PARENT/'pair-state.json')=='04832cc18c11ad9da49d2cfc0c865baed07a18ace44d1de9d8319b150890e7dd' and H(PARENT/'author/state.json')=='b9ab036bf00296c9491ef6f06eb44aca805b51ab36f0d48e090d5620a55f6153' and H(SNAP/'manifest.json')=='63b846158674d41beeaa99843d92008465f8e0fe5c45bb9e1fed4b78e1a2ab48' and H(PROVIDER)=='7cbd49b6d84497c46520e908fc8c4dc105d7a0070fd1323c6c28e26bf4cf00f6' and H(LEAN)=='e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550'
prior=J(PRIOR/'receipt.json');pt=J(PRIOR/'terminal-observation.json');assert pt['exit_code']==0 and pt['receipt_sha256']==H(PRIOR/'receipt.json') and prior['author_state_sha256']==H(PARENT/'author/state.json')
parent=J(PARENT/'author/state.json');manifest=J(SNAP/'manifest.json');provider=J(PROVIDER);assert parent['status']=='PASS' and provider['status']=='BUILT' and provider['exit_code']==0
seen=set();todo=['DiophantineConsistency.ArithmeticAdaptiveFactorThree2011','DiophantineConsistency.ArithmeticAdaptiveMersenne2011']
while todo:
 n=todo.pop()
 if n in seen or n not in manifest['sources']:continue
 seen.add(n);todo.extend(manifest['sources'][n]['imports'])
assert len(seen)==62;records={x['module']:x for x in parent['records']};tracked={};absent=set()
for n in seen:
 row=manifest['sources'][n];assert H(SNAP/row['snapshot_path'])==row['sha256']==records[n]['source_sha256'] and records[n]['exit']==0 and H(records[n]['log'])==records[n]['log_sha256']
 for path,meta in parent['outputs'][n].items():
  q=Path(path)
  if meta is None:assert not os.path.lexists(q);absent.add(path)
  else:assert q.is_file() and not q.is_symlink() and str(q.resolve())==meta['realpath'] and H(q)==meta['sha256'];tracked[path]=meta['sha256']
assert len(tracked)==62 and len(absent)==558
factor=(SNAP/manifest['sources']['DiophantineConsistency.ArithmeticAdaptiveFactorThree2011']['snapshot_path']).read_text();mersenne=(SNAP/manifest['sources']['DiophantineConsistency.ArithmeticAdaptiveMersenne2011']['snapshot_path']).read_text()
assert 'theorem cancel_factor_three (q Y X t : V) (hq : 0<q)' in factor and '(hY : q^3∣Y) (hd : q^5∣(3+4*Y*(X+1))*t) : q^4∣t' in factor
assert 'theorem cancel_three (d R q J : V) (hd : 4≤d)' in mersenne and '(hq : q=(Exp.exp d-1)*J+1) (hdiv : q∣3*Exp.exp R) : q∣Exp.exp R' in mersenne
rx=re.compile(r"^'([^']+)' depends on axioms: \[([^\]]*)\]",re.M|re.S);expected=['conditional_compact44_cancellations','conditional_freeJ_split_and_cancellations'];results={}
for label,out,receipt,pin in [('original',ORIG,TASK/'replay-receipt.json','955f79233a43e2500aa2f477a51bc097ad419604b2306e908ff9fd54236d2a06'),('independent',FRESH,FRESH_RECEIPT,'af62476a18442067e088d3d611937e12b18e26815a300b82684c8de1db929348')]:
 d=J(receipt);assert H(receipt)==pin and d['status']=='PASS_BOUNDED_CONDITIONAL_FREEJ_RANK_ADAPTER' and d['freej_replay_exit_code']==d['lean_exit_code']==d['deps_exit_code']==0 and set(d['source_closure'])==seen and set(d['absent_parent_paths'])==absent and {x['source'] for x in d['seed_links'].values()}==set(tracked)
 for link,meta in d['seed_links'].items():
  q=Path(link);src=Path(meta['source']);assert q==(out/'freej/concrete/composed/base/lib'/src.relative_to(PARENT/'author/lib')) and q.is_symlink() and q.resolve()==src.resolve() and H(q)==meta['sha256']==tracked[str(src)]
 assert all(not os.path.lexists(x) for x in absent)
 inner=J(out/'freej-receipt.json');assert H(out/'freej-receipt.json')==d['freej_receipt_sha256'] and inner==d['freej_receipt'] and inner['status']=='PASS_BOUNDED_FREE_J_95_FACTOR_SPLIT'
 lib=out/'freej/concrete/composed/base/lib/DiophantineConsistency';free_src=out/'freej/src/DiophantineConsistency/Ordinary12FreeJ.lean';free_obj=lib/'Ordinary12FreeJ.olean';assert H(free_src)==H(FREEJ/'Ordinary12FreeJ.lean')==fa['results']['original']['source_sha256'] and H(free_obj)==inner['object_sha256']==fa['results']['original']['object_sha256']
 for name,sha in inner['inner_receipt']['generated_objects'].items():assert H(lib/(name+'.olean'))==sha==fa['results']['original']['generated_objects'][name]
 src=out/'src/DiophantineConsistency/Ordinary12RankAdapter.lean';obj=out/'Ordinary12RankAdapter.olean';assert H(src)==H(TASK/'Ordinary12RankAdapter.lean') and H(obj)==d['object_sha256']=='65fdb3280c890585b442c8f6148bc902ee87d06787b13e1e937c8445cc21eec2' and not obj.is_symlink()
 log=d['lean_stdout']+d['lean_stderr'];matches=rx.findall(log);assert [n for n,_ in matches]==['DiophantineConsistency.Ordinary12RankAdapter.'+n for n in expected] and all({x.strip() for x in v.split(',')}<={'propext','Classical.choice','Quot.sound'} for _,v in matches) and 'sorryAx' not in log and 'warning:' not in log
 env=os.environ.copy()
 for n in ('LEAN_SRC_PATH','LEAN_SYSROOT','LD_LIBRARY_PATH','LD_PRELOAD','LD_AUDIT'):env.pop(n,None)
 env['LEAN_PATH']=str(out/'freej/concrete/composed/base/lib')+':'+str(PACKAGE)
 deps=subprocess.run([str(LEAN),'--deps',str(src)],env=env,capture_output=True,text=True,timeout=60);assert deps.returncode==0 and deps.stdout==d['deps_stdout']
 required={str(PACKAGE/'Init.olean')}|{str(lib/(n+'.olean')) for n in ('Ordinary12FreeJ','ArithmeticAdaptiveFactorThree2011','ArithmeticAdaptiveMersenne2011')};assert set(deps.stdout.splitlines())==required
 assert H(PACKAGE/'Init.olean')==parent['guarded_companions'][str(PACKAGE/'Init.olean')]['sha256']
 for path,sha in d['script_hashes'].items():assert H(path)==sha
 results[label]={'receipt_sha256':H(receipt),'freej_receipt_sha256':H(out/'freej-receipt.json'),'source_sha256':H(src),'object_sha256':H(obj),'log_sha256':RAW(log),'direct_inputs_sha256':{str(Path(q).resolve()):H(q) for q in deps.stdout.splitlines()},'linked_objects':len(d['seed_links']),'absent_companions':len(d['absent_parent_paths'])}
assert results['original']['object_sha256']==results['independent']['object_sha256'] and results['original']['log_sha256']==results['independent']['log_sha256']
assert before=={str(p.resolve()):H(p) for p in files}
out={'status':'PASS_INDEPENDENT_ORDINARY12_RANK_ADAPTER_ARTIFACT_AUDIT','inputs_sha256':before,'closure_modules':len(seen),'parent_objects':len(tracked),'absent_companions':len(absent),'statement_mutations_rejected':len(mutations),'divisible_by_three_positive_control':True,'results':results,'scope':'Conditional historical IΣ₁-model adapter with separate carrier divisibility and Mersenne-equality assumptions; no graph-to-carrier bindings, rank derivation, compact44 calibration, matched full project replay or internal iPRA proof.'};path=HERE/'receipt.json'
if path.exists():raise ValueError('refusing receipt overwrite')
path.write_text(json.dumps(out,sort_keys=True,indent=2)+'\n');print(out['status'],H(path))
