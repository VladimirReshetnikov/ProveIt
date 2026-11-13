#!/usr/bin/env python3
"""Independent q graph-binding theorem and bounded replay artifact audit."""
import hashlib,json,os,re,subprocess
from pathlib import Path
if not __debug__:raise RuntimeError('independent audit requires assertions enabled')
HERE=Path(__file__).resolve().parent;ROOT=HERE.parents[3];BASE=ROOT/'Computability/DiophantineConsistency';TASK=BASE/'research/ordinary12-ipra-bridge/free-j-q-binding-prototype';RANK=TASK.parent/'rank-adapter-prototype';FREEJ=TASK.parent/'free-j-prototype';GRAPH=BASE/'con-zfc-diophantine-forms/115-synchronized-exponents/supplement/circuits/positive12_95_degree70.json';ORIG=Path('/tmp/ipra-ordinary12-q-binding-replay-01');FRESH=Path('/tmp/ipra-ordinary12-q-binding-independent-replay-02');FRESH_RECEIPT=Path('/tmp/ipra-ordinary12-q-binding-independent-replay-02-receipt.json');PARENT=Path('/tmp/ipra-aq29-fresh-project-pair');SNAP=Path('/tmp/ipra-aq29-fresh-source-closure-v2');PROVIDER=Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/build-all-receipt.json');PACKAGE=Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib');LEAN=Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean');PA=BASE/'reviews/fresh-project-pair-independent-audit';RA=BASE/'reviews/ordinary12-rank-adapter-independent-audit';FA=BASE/'reviews/ordinary12-freej-prototype-independent-audit';MA=BASE/'reviews/manuscript115-reconstruction-independent-audit'
H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest();J=lambda p:json.loads(Path(p).read_text());RAW=lambda s:hashlib.sha256(s.encode()).hexdigest()
files=[Path(__file__),TASK/'FreeJQBinding.lean',TASK/'replay.py',TASK/'replay-receipt.json',TASK/'README.md',RANK/'Ordinary12RankAdapter.lean',RANK/'replay.py',FREEJ/'Ordinary12FreeJ.lean',GRAPH,FRESH_RECEIPT,PARENT/'pair-state.json',PARENT/'author/state.json',SNAP/'manifest.json',PROVIDER,LEAN,PA/'receipt.json',PA/'terminal-observation.json',RA/'receipt.json',RA/'terminal-observation.json',FA/'receipt.json',FA/'terminal-observation.json',MA/'receipt.json',MA/'terminal-observation.json']
before={str(p.resolve()):H(p) for p in files};assert H(TASK/'FreeJQBinding.lean')=='02b300a94191430bb4580525605e5070ae6f13fd083c38ff8cfdddb0da9e7a5a' and H(TASK/'replay-receipt.json')=='17dd9ce902ae31b9756246c3754408c98a4ee4c8e240d5d31b432b4f6b137866' and H(FRESH_RECEIPT)=='f72b7f1fa9484aaafd50f4e43849d9280df4cc30fd98cbf9c609110304e654ee'
for f in (TASK/'FreeJQBinding.lean',TASK/'replay.py',TASK/'replay-receipt.json',TASK/'README.md'):
 assert hashlib.sha256(subprocess.check_output(['git','show','1f4ed70acb:'+str(f.relative_to(ROOT))],cwd=ROOT)).hexdigest()==H(f)
# Pin the separate audited graph and actual beta bytes; this is not a model
# proof of equality between the literal port and the internal exponential.
ma=J(MA/'receipt.json');mt=J(MA/'terminal-observation.json');assert H(MA/'receipt.json')=='7c2280abbe67a3fd499f77193490d98c5c3d6f3aaf1a320d8542dae2dfb882ab' and mt['observed_exit_code']==0 and mt['receipt_sha256']==H(MA/'receipt.json') and ma['status']=='PASS_INDEPENDENT_MANUSCRIPT115_RECONSTRUCTION_REVIEW'
assert ma['ports']['beta']['raw_sha256']=='0664a868cbfef9869ea05c40a1c445563f685ff857092594c1c1223bc4b21f9d' and ma['ports']['beta']['bits']==590069
assert H(GRAPH)=='2348183cb8e366433f668cdcc9d77ca9c7e2d0c55b7b630bda39bd8db7506d22' and H(FREEJ/'Ordinary12FreeJ.lean')=='542bb6913f5b7e6d1ef3cd9e430fcbee20ee727966d3bfc9f2b6d71c566ef96a'
g=J(GRAPH);assert g['witnesses'][0]=='J' and g['fixed_numerals']==['beta','K0','MC','MF'] and g['source'][0]==['qm','*','J','beta'] and g['source'][1]==['q','+',1,'qm']
f=(FREEJ/'Ordinary12FreeJ.lean').read_text();assert '  let J : Expr (Fin 12) := .var 0\n' in f and '  let beta : Expr (Fin 12) := .constant (p 0)\n' in f and '  let qm := J * beta\n' in f and '  let q := 1 + qm\n' in f
source=(TASK/'FreeJQBinding.lean').read_text();assert 'variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]' in source
def statement(s,name):
 x=s.split('theorem '+name,1)
 if len(x)!=2:raise ValueError('missing theorem')
 return ' '.join(x[1].split(':= by',1)[0].split())
def validate(s):
 expected={
  'qm_binding':'(p : Fin 4 → ℤ) (v : Fin 12 → V) (hbeta : 0 ≤ p 0) : Equivalent (pairEval (core p).qm v) (natural (v 0 * ((p 0).toNat : V)))',
  'q_binding':'(p : Fin 4 → ℤ) (v : Fin 12 → V) (hbeta : 0 ≤ p 0) : pairEval (1+(core p).qm) v = natural (1 + v 0 * ((p 0).toNat : V))',
  'q_positive':'(p : Fin 4 → ℤ) (v : Fin 12 → V) (hbeta : 0 ≤ p 0) : 0 < (pairEval (1+(core p).qm) v).1',
  'graphQ_eq':'(p : Fin 4 → ℤ) (v : Fin 12 → V) (hbeta : 0 ≤ p 0) : graphQ p v = ((p 0).toNat : V) * v 0 + 1',
  'graph_cancellations':'(p : Fin 4 → ℤ) (v : Fin 12 → V) (hbeta : 0 ≤ p 0) (hport : ((p 0).toNat : V) = Exp.exp (590069:V)-1) (Y X t R : V) (hY : graphQ p v ^ 3 ∣ Y) (hH : graphQ p v ^ 5 ∣ (3+4*Y*(X+1))*t) (h3 : graphQ p v ∣ 3*Exp.exp R) : graphQ p v ^ 4 ∣ t ∧ graphQ p v ∣ Exp.exp R'}
 for n,e in expected.items():
  if statement(s,n)!=e:raise ValueError(('theorem changed',n))
 if 'def graphQ (p : Fin 4 → ℤ) (v : Fin 12 → V) : V :=\n  (pairEval (1+(core p).qm) v).1' not in s:raise ValueError('graphQ definition')
 if 'conditional_compact44_cancellations (graphQ p v) Y X t R (v 0) hqpos hY hH hq h3' not in s:raise ValueError('branch premises')
validate(source)
mutations=[('v 0 * ((p 0).toNat : V)','v 1 * ((p 0).toNat : V)'),('0 ≤ p 0','0 ≤ p 1'),('590069:V','590068:V'),('graphQ p v ^ 3 ∣ Y','graphQ p v ^ 2 ∣ Y'),('graphQ p v ∣ 3*Exp.exp R','graphQ p v ∣ Exp.exp R')]
for a,b in mutations:
 assert a in source
 try:validate(source.replace(a,b,1))
 except ValueError:pass
 else:raise AssertionError(('mutation accepted',a))
# Independent arithmetic sanity checks for nonnegative beta, including zero,
# plus a negative-beta counterexample to omitting the nonnegativity premise.
for j in range(5):
 for beta in range(5):
  positive=(1+j*max(beta,0),j*max(-beta,0));assert positive==(1+j*beta,0) and positive[0]>0
assert (1+2*max(-1,0),2*max(1,0))!=(1+2*max(-1,0),0)
ra=J(RA/'receipt.json');rt=J(RA/'terminal-observation.json');assert H(RA/'receipt.json')=='212fa3881f1dd7e514429c8e6273543e5b25be6d3f6000e780dff16b11774b42' and rt['audit_observed_exit_code']==0 and rt['receipt_sha256']==H(RA/'receipt.json') and ra['status']=='PASS_INDEPENDENT_ORDINARY12_RANK_ADAPTER_ARTIFACT_AUDIT'
fa=J(FA/'receipt.json');ft=J(FA/'terminal-observation.json');assert H(FA/'receipt.json')=='9fa181917cfd6246c4dc8f305d8ced81cc1c6baf628adc97d6e78e43ec42c706' and ft['audit_observed_exit_code']==0 and ft['receipt_sha256']==H(FA/'receipt.json') and fa['status']=='PASS_INDEPENDENT_ORDINARY12_FREE_J_ARTIFACT_AUDIT'
assert H(PARENT/'pair-state.json')=='04832cc18c11ad9da49d2cfc0c865baed07a18ace44d1de9d8319b150890e7dd' and H(PARENT/'author/state.json')=='b9ab036bf00296c9491ef6f06eb44aca805b51ab36f0d48e090d5620a55f6153' and H(SNAP/'manifest.json')=='63b846158674d41beeaa99843d92008465f8e0fe5c45bb9e1fed4b78e1a2ab48' and H(PROVIDER)=='7cbd49b6d84497c46520e908fc8c4dc105d7a0070fd1323c6c28e26bf4cf00f6' and H(LEAN)=='e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550'
pa=J(PA/'receipt.json');pt=J(PA/'terminal-observation.json');assert pt['exit_code']==0 and pt['receipt_sha256']==H(PA/'receipt.json') and pa['author_state_sha256']==H(PARENT/'author/state.json')
parent=J(PARENT/'author/state.json');manifest=J(SNAP/'manifest.json');seen=set();todo=['DiophantineConsistency.ArithmeticAdaptiveFactorThree2011','DiophantineConsistency.ArithmeticAdaptiveMersenne2011']
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
rx=re.compile(r"^'([^']+)' depends on axioms: \[([^\]]*)\]",re.M|re.S);expected=['qm_binding','q_binding','q_positive','graphQ_eq','graph_cancellations'];results={}
for label,out,receipt,pin in [('original',ORIG,TASK/'replay-receipt.json','17dd9ce902ae31b9756246c3754408c98a4ee4c8e240d5d31b432b4f6b137866'),('independent',FRESH,FRESH_RECEIPT,'f72b7f1fa9484aaafd50f4e43849d9280df4cc30fd98cbf9c609110304e654ee')]:
 d=J(receipt);assert H(receipt)==pin and d['status']=='PASS_BOUNDED_FREEJ_Q_GRAPH_BINDING' and d['inner_exit_code']==d['lean_exit_code']==d['deps_exit_code']==0
 rank=J(out/'rank-receipt.json');assert H(out/'rank-receipt.json')==d['inner_receipt_sha256'] and rank==d['inner_receipt'] and rank['status']=='PASS_BOUNDED_CONDITIONAL_FREEJ_RANK_ADAPTER'
 assert set(rank['source_closure'])==seen and set(rank['absent_parent_paths'])==absent and {x['source'] for x in rank['seed_links'].values()}==set(tracked)
 for link,meta in rank['seed_links'].items():
  q=Path(link);src=Path(meta['source']);assert q==(out/'rank/freej/concrete/composed/base/lib'/src.relative_to(PARENT/'author/lib')) and q.is_symlink() and q.resolve()==src.resolve() and H(q)==meta['sha256']==tracked[str(src)]
 assert all(not os.path.lexists(x) for x in absent)
 rank_src=out/'rank/src/DiophantineConsistency/Ordinary12RankAdapter.lean';rank_obj=out/'rank/Ordinary12RankAdapter.olean';lib=out/'rank/freej/concrete/composed/base/lib/DiophantineConsistency';rank_copy=lib/'Ordinary12RankAdapter.olean'
 assert H(rank_src)==H(RANK/'Ordinary12RankAdapter.lean') and H(rank_obj)==H(rank_copy)==d['rank_seed_sha256']==rank['object_sha256']==ra['results']['original']['object_sha256'] and not rank_copy.is_symlink() and (rank_obj.stat().st_dev,rank_obj.stat().st_ino)!=(rank_copy.stat().st_dev,rank_copy.stat().st_ino)
 rank_log=rank['lean_stdout']+rank['lean_stderr'];assert RAW(rank_log)==ra['results']['original']['log_sha256'] and 'sorryAx' not in rank_log and 'warning:' not in rank_log
 free_obj=lib/'Ordinary12FreeJ.olean';assert H(free_obj)==fa['results']['original']['object_sha256']
 src=out/'src/DiophantineConsistency/FreeJQBinding.lean';obj=out/'FreeJQBinding.olean';assert H(src)==H(TASK/'FreeJQBinding.lean') and H(obj)==d['object_sha256']=='e44a139a2a1bce5806bfc99b6fb811d0ffab278d520078e5e1ac7e65b90f6046' and not obj.is_symlink()
 log=d['lean_stdout']+d['lean_stderr'];matches=rx.findall(log);assert [n for n,_ in matches]==['FreeJQBinding.'+n for n in expected] and all({x.strip() for x in v.split(',')}<={'propext','Classical.choice','Quot.sound'} for _,v in matches) and 'sorryAx' not in log and 'warning:' not in log
 env=os.environ.copy()
 for n in ('LEAN_SRC_PATH','LEAN_SYSROOT','LD_LIBRARY_PATH','LD_PRELOAD','LD_AUDIT'):env.pop(n,None)
 env['LEAN_PATH']=str(out/'rank/freej/concrete/composed/base/lib')+':'+str(PACKAGE)
 for file,saved,expected_paths in [(src,d['deps_stdout'],{str(PACKAGE/'Init.olean'),str(free_obj),str(rank_copy)}),(rank_src,rank['deps_stdout'],{str(PACKAGE/'Init.olean'),str(free_obj),str(lib/'ArithmeticAdaptiveFactorThree2011.olean'),str(lib/'ArithmeticAdaptiveMersenne2011.olean')})]:
  deps=subprocess.run([str(LEAN),'--deps',str(file)],env=env,capture_output=True,text=True,timeout=60);assert deps.returncode==0 and deps.stdout==saved and set(deps.stdout.splitlines())==expected_paths
 assert H(PACKAGE/'Init.olean')==parent['guarded_companions'][str(PACKAGE/'Init.olean')]['sha256']
 for path,sha in d['inputs_sha256'].items():assert H(path)==sha
 results[label]={'receipt_sha256':H(receipt),'rank_receipt_sha256':H(out/'rank-receipt.json'),'rank_source_sha256':H(rank_src),'rank_object_sha256':H(rank_obj),'source_sha256':H(src),'object_sha256':H(obj),'log_sha256':RAW(log),'direct_inputs_sha256':{str(Path(q).resolve()):H(q) for q in (str(PACKAGE/'Init.olean'),str(free_obj),str(rank_copy))},'linked_objects':len(rank['seed_links']),'absent_companions':len(rank['absent_parent_paths'])}
assert results['original']['object_sha256']==results['independent']['object_sha256'] and results['original']['log_sha256']==results['independent']['log_sha256']
assert before=={str(p.resolve()):H(p) for p in files}
out={'status':'PASS_INDEPENDENT_FREE_J_Q_BINDING_ARTIFACT_AUDIT','inputs_sha256':before,'graph_rows':95,'statement_mutations_rejected':len(mutations),'nonnegative_beta_cases':25,'negative_beta_control':True,'closure_modules':len(seen),'parent_objects':len(tracked),'absent_companions':len(absent),'results':results,'scope':'Bounded historical single-author q graph binding; actual model port equality and all divisibility hypotheses remain explicit; no rank derivation, checker calibration, matched full project replay or iPRA proof.'};path=HERE/'receipt.json'
if path.exists():raise ValueError('refusing receipt overwrite')
path.write_text(json.dumps(out,sort_keys=True,indent=2)+'\n');print(out['status'],H(path))
