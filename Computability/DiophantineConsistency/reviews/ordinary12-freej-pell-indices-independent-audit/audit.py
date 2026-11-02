#!/usr/bin/env python3
"""Independent q graph-binding theorem and bounded replay artifact audit."""
import hashlib,json,os,re,subprocess
from pathlib import Path
if not __debug__:raise RuntimeError('independent audit requires assertions enabled')
HERE=Path(__file__).resolve().parent;ROOT=HERE.parents[3];BASE=ROOT/'Computability/DiophantineConsistency';TASK=BASE/'research/ordinary12-ipra-bridge/free-j-pell-indices-prototype';RANK=TASK.parent/'rank-adapter-prototype';FREEJ=TASK.parent/'free-j-prototype';GRAPH=BASE/'con-zfc-diophantine-forms/115-synchronized-exponents/supplement/circuits/positive12_95_degree70.json';ORIG=Path('/tmp/ipra-ordinary12-pell-indices-replay-01');FRESH=Path('/tmp/ipra-freej-pell-indices-independent-replay-02');FRESH_RECEIPT=Path('/tmp/ipra-freej-pell-indices-independent-replay-02-receipt.json');PARENT=Path('/tmp/ipra-aq29-fresh-project-pair');SNAP=Path('/tmp/ipra-aq29-fresh-source-closure-v2');PROVIDER=Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/build-all-receipt.json');PACKAGE=Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib');LEAN=Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean');PA=BASE/'reviews/fresh-project-pair-independent-audit';RA=BASE/'reviews/ordinary12-rank-adapter-independent-audit';FA=BASE/'reviews/ordinary12-freej-prototype-independent-audit';MA=BASE/'reviews/manuscript115-reconstruction-independent-audit'
H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest();J=lambda p:json.loads(Path(p).read_text());RAW=lambda s:hashlib.sha256(s.encode()).hexdigest()
files=[Path(__file__),TASK/'FreeJPellIndices.lean',TASK/'replay.py',TASK/'replay-receipt.json',TASK/'README.md',RANK/'Ordinary12RankAdapter.lean',RANK/'replay.py',FREEJ/'Ordinary12FreeJ.lean',GRAPH,FRESH_RECEIPT,PARENT/'pair-state.json',PARENT/'author/state.json',SNAP/'manifest.json',PROVIDER,LEAN,PA/'receipt.json',PA/'terminal-observation.json',RA/'receipt.json',RA/'terminal-observation.json',FA/'receipt.json',FA/'terminal-observation.json',MA/'receipt.json',MA/'terminal-observation.json']
before={str(p.resolve()):H(p) for p in files};assert H(TASK/'FreeJPellIndices.lean')=='8d222d5302d22c914694dbe36478870af9358b0a26046a8135a0b26c1ac4bf72' and H(TASK/'replay-receipt.json')=='d0c9bde096771d76b05e6cb1e4f0b9cda2791ea50a35ea5c1abe3141d5e68de6' and H(FRESH_RECEIPT)=='7474b4278bc1cb465543ff3e0e089610ead2fc2892f4f97cd7143258ee8c632d'
for f in (TASK/'FreeJPellIndices.lean',TASK/'replay.py',TASK/'replay-receipt.json',TASK/'README.md'):
 assert hashlib.sha256(subprocess.check_output(['git','show','f7658ac84c:'+str(f.relative_to(ROOT))],cwd=ROOT)).hexdigest()==H(f)
# Pin the separate audited graph and actual beta bytes; this is not a model
# proof of equality between the literal port and the internal exponential.
ma=J(MA/'receipt.json');mt=J(MA/'terminal-observation.json');assert H(MA/'receipt.json')=='7c2280abbe67a3fd499f77193490d98c5c3d6f3aaf1a320d8542dae2dfb882ab' and mt['observed_exit_code']==0 and mt['receipt_sha256']==H(MA/'receipt.json') and ma['status']=='PASS_INDEPENDENT_MANUSCRIPT115_RECONSTRUCTION_REVIEW'
assert ma['ports']['beta']['raw_sha256']=='0664a868cbfef9869ea05c40a1c445563f685ff857092594c1c1223bc4b21f9d' and ma['ports']['beta']['bits']==590069
assert H(GRAPH)=='2348183cb8e366433f668cdcc9d77ca9c7e2d0c55b7b630bda39bd8db7506d22' and H(FREEJ/'Ordinary12FreeJ.lean')=='542bb6913f5b7e6d1ef3cd9e430fcbee20ee727966d3bfc9f2b6d71c566ef96a'
g=J(GRAPH);assert g['witnesses'][0]=='J' and g['fixed_numerals']==['beta','K0','MC','MF'] and g['source'][0]==['qm','*','J','beta'] and g['source'][1]==['q','+',1,'qm']
f=(FREEJ/'Ordinary12FreeJ.lean').read_text();assert '  let J : Expr (Fin 12) := .var 0\n' in f and '  let beta : Expr (Fin 12) := .constant (p 0)\n' in f and '  let qm := J * beta\n' in f and '  let q := 1 + qm\n' in f
q3=BASE/'reviews/ordinary12-freej-first-divisibility-independent-audit';assert H(q3/'receipt.json')=='99af74f6739cfadc3136506742902e06e42fc096f8e04106c1e538ebdf9b5ae1' and J(q3/'terminal-observation.json')['audit_observed_exit_code']==0
tr=BASE/'reviews/ordinary12-freej-first-transport-independent-audit';assert H(tr/'receipt.json')=='c107806a59475e77cb64cbc68cad4a1e0bbdd903314994f6985c7554d5bde8e5' and J(tr/'terminal-observation.json')['audit_observed_exit_code']==0
mainaudit=BASE/'reviews/ordinary12-freej-main-congruence-independent-audit';assert H(mainaudit/'receipt.json')=='9e2c89ab61a2114a5755a820904b219990cb4748126ff08381169b6e47697803' and J(mainaudit/'terminal-observation.json')['audit_observed_exit_code']==0
source=(TASK/'FreeJPellIndices.lean').read_text()
assert 'variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]' in source
def validate(s):
 head=' '.join(s.split('theorem indices',1)[1].split(':= by',1)[0].split())
 if head != '(p : Fin 4 → ℕ) (v : Fin 12 → V) (hb : 0<(p 0:V)) (hv : ∀j,0<v j) (hz : InternalZero (literal (fun j => (p j:ℤ))) v) : FreeJIndices p v':raise ValueError('wrong theorem statement')
 stmt=' '.join(s.split('def FreeJIndices',1)[1].split('theorem indices',1)[0].split())
 want='(p : Fin 4 → ℕ) (v : Fin 12 → V) : Prop := let q : V := 1+v 0*(p 0:V) let M : V := (q*(q*q))*(v 0*(p 0:V)) let U : V := v 6*(q*q) let Q : V := (v 5*v 6)*v 6 let k : V := v 8+v 9 let c : V := v 8+v 6*k let a : V := v 5*v 6+v 6 ∃ first main n m : V, 0<first ∧ 0<main ∧ 0<n ∧ 0<m ∧ n≤k ∧ m≤c ∧ magnitude (pairEval (core (fun j => (p j:ℤ))).z v)=M*first ∧ Equivalent (pairEval (core (fun j => (p j:ℤ))).d v) (natural (U*main)) ∧ xcoord n (2*(Q-1)+1)=first ∧ 2*ycoord n (2*(Q-1)+1)=k ∧ xcoord m a=main ∧ ycoord m a=c'
 if stmt!=want:raise ValueError('wrong indices definition')
 for x in ['scaled_quotient _ _ _ hM (first_scaled_norm p v hz)','main_oriented p v hb hv hz','ArithmeticPellFirstNorm.positive_parameter_solution Q first k hQ hn','ArithmeticPellClassification.solution_index a main c hmn']:
  if x not in s:raise ValueError(('missing proof call',x))
validate(source)
mutations=[('0<(p 0:V)','0<(p 1:V)'),('∀j,0<v j','∀j,0≤v j'),('2*ycoord n (2*(Q-1)+1)=k','ycoord n (2*(Q-1)+1)=k'),('ycoord m a=c','ycoord n a=c'),('n≤k ∧ m≤c','n≤c ∧ m≤k')]
for a,b in mutations:
 assert a in source
 try:validate(source.replace(a,b))
 except ValueError:pass
 else:raise AssertionError(('mutation accepted',a))
# Exact algebraic conversion checked on bounded natural inputs; the Lean ring
# proof supplies universal identity, not these finite examples.
for Q in range(1,21):
 for k in range(21):assert (Q*k)*(Q*k+k)==Q*(Q+1)*k*k
for a in range(30):assert (3+4*a)+a*a==(a+1)*(a+3)
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
rx=re.compile(r"^'([^']+)' depends on axioms: \[([^\]]*)\]",re.M|re.S);expected=['indices'];results={}
for label,out,receipt,pin in [('original',ORIG,TASK/'replay-receipt.json','d0c9bde096771d76b05e6cb1e4f0b9cda2791ea50a35ea5c1abe3141d5e68de6'),('independent',FRESH,FRESH_RECEIPT,'7474b4278bc1cb465543ff3e0e089610ead2fc2892f4f97cd7143258ee8c632d')]:
 d=J(receipt);assert H(receipt)==pin and d['status']=='PASS_BOUNDED_FREEJ_PELL_INDICES' and d['inner_exit_code']==d['lean_exit_code']==d['deps_exit_code']==0
 main=J(out/'rank-receipt.json');assert H(out/'rank-receipt.json')==d['inner_receipt_sha256'] and main==d['inner_receipt'] and main['status']=='PASS_BOUNDED_FREEJ_MAIN_RANK_CONGRUENCE'
 transport=main['inner_receipt'];assert transport['status']=='PASS_BOUNDED_FREEJ_FIRST_TRANSPORT' and H(out/'rank/rank-receipt.json')==main['inner_receipt_sha256']
 first=transport['inner_receipt'];assert first['status']=='PASS_BOUNDED_FREEJ_FIRST_DIVISIBILITY' and H(out/'rank/rank/rank-receipt.json')==transport['inner_receipt_sha256']
 rank=first['inner_receipt'];assert rank['status']=='PASS_BOUNDED_CONDITIONAL_FREEJ_RANK_ADAPTER' and H(out/'rank/rank/rank/rank-receipt.json')==first['inner_receipt_sha256']
 assert set(rank['source_closure'])==seen and set(rank['absent_parent_paths'])==absent and {x['source'] for x in rank['seed_links'].values()}==set(tracked)
 for link,meta in rank['seed_links'].items():
  q=Path(link);src=Path(meta['source']);assert q==(out/'rank/rank/rank/rank/freej/concrete/composed/base/lib'/src.relative_to(PARENT/'author/lib')) and q.is_symlink() and q.resolve()==src.resolve() and H(q)==meta['sha256']==tracked[str(src)]
 assert all(not os.path.lexists(x) for x in absent)
 rank_src=out/'rank/rank/rank/rank/src/DiophantineConsistency/Ordinary12RankAdapter.lean';rank_obj=out/'rank/rank/rank/rank/Ordinary12RankAdapter.olean';lib=out/'rank/rank/rank/rank/freej/concrete/composed/base/lib/DiophantineConsistency';rank_copy=lib/'Ordinary12RankAdapter.olean'
 assert H(rank_src)==H(RANK/'Ordinary12RankAdapter.lean') and H(rank_obj)==H(rank_copy)==first['rank_seed_sha256']==rank['object_sha256']==ra['results']['original']['object_sha256'] and not rank_copy.is_symlink() and (rank_obj.stat().st_dev,rank_obj.stat().st_ino)!=(rank_copy.stat().st_dev,rank_copy.stat().st_ino)
 rank_log=rank['lean_stdout']+rank['lean_stderr'];assert RAW(rank_log)==ra['results']['original']['log_sha256'] and 'sorryAx' not in rank_log and 'warning:' not in rank_log
 free_obj=lib/'Ordinary12FreeJ.olean';assert H(free_obj)==fa['results']['original']['object_sha256']
 first_seed=out/'rank/rank/rank/FreeJRootBinding.olean';first_copy=lib/'FreeJRootBinding.olean'
 assert H(first_seed)==H(first_copy)==transport['rank_seed_sha256']==first['object_sha256']=='58860b9c6f256a15df038991edc682af4b4c831ab0ae3c3565f1f14ea4833b40' and not first_copy.is_symlink() and (first_seed.stat().st_dev,first_seed.stat().st_ino)!=(first_copy.stat().st_dev,first_copy.stat().st_ino)
 transport_seed=out/'rank/rank/FreeJFirstTransport.olean';transport_copy=lib/'FreeJFirstTransport.olean'
 assert H(transport_seed)==H(transport_copy)==main['rank_seed_sha256']==transport['object_sha256']=='79be848e07657adfb949dcbfe87ff993ee73a957f65713344d374d83540a3df8' and not transport_copy.is_symlink() and (transport_seed.stat().st_dev,transport_seed.stat().st_ino)!=(transport_copy.stat().st_dev,transport_copy.stat().st_ino)
 main_seed=out/'rank/FreeJMainOrientation.olean';main_copy=lib/'FreeJMainOrientation.olean'
 assert H(main_seed)==H(main_copy)==d['rank_seed_sha256']==main['object_sha256']=='62a60121277c2aa71ebc457023dc4315fcf8855f614e89b5814350cc4dcf131c' and not main_copy.is_symlink() and (main_seed.stat().st_dev,main_seed.stat().st_ino)!=(main_copy.stat().st_dev,main_copy.stat().st_ino)
 src=out/'src/DiophantineConsistency/FreeJPellIndices.lean';obj=out/'FreeJPellIndices.olean';assert H(src)==H(TASK/'FreeJPellIndices.lean') and H(obj)==d['object_sha256']=='20b39ea983c17d69b0edc4ab9a0b4239f685c2c250418c04e4c9ae2ad8dc07cb' and not obj.is_symlink()
 log=d['lean_stdout']+d['lean_stderr'];matches=rx.findall(log);assert [n for n,_ in matches]==['FreeJPellIndices.'+n for n in expected] and all({x.strip() for x in v.split(',')}<={'propext','Classical.choice','Quot.sound'} for _,v in matches) and 'sorryAx' not in log and 'warning:' not in log
 env=os.environ.copy()
 for n in ('LEAN_SRC_PATH','LEAN_SYSROOT','LD_LIBRARY_PATH','LD_PRELOAD','LD_AUDIT'):env.pop(n,None)
 env['LEAN_PATH']=str(out/'rank/rank/rank/rank/freej/concrete/composed/base/lib')+':'+str(PACKAGE)
 for file,saved,expected_paths in [(src,d['deps_stdout'],{str(PACKAGE/'Init.olean'),str(main_copy),str(lib/'ArithmeticAdaptivePellIndices2011.olean')}),(rank_src,rank['deps_stdout'],{str(PACKAGE/'Init.olean'),str(free_obj),str(lib/'ArithmeticAdaptiveFactorThree2011.olean'),str(lib/'ArithmeticAdaptiveMersenne2011.olean')})]:
  deps=subprocess.run([str(LEAN),'--deps',str(file)],env=env,capture_output=True,text=True,timeout=60);assert deps.returncode==0 and deps.stdout==saved and set(deps.stdout.splitlines())==expected_paths
 assert H(PACKAGE/'Init.olean')==parent['guarded_companions'][str(PACKAGE/'Init.olean')]['sha256']
 for path,sha in d['inputs_sha256'].items():assert H(path)==sha
 results[label]={'receipt_sha256':H(receipt),'rank_receipt_sha256':H(out/'rank-receipt.json'),'rank_source_sha256':H(rank_src),'rank_object_sha256':H(rank_obj),'source_sha256':H(src),'object_sha256':H(obj),'log_sha256':RAW(log),'direct_inputs_sha256':{str(Path(q).resolve()):H(q) for q in (str(PACKAGE/'Init.olean'),str(main_copy),str(lib/'ArithmeticAdaptivePellIndices2011.olean'))},'linked_objects':len(rank['seed_links']),'absent_companions':len(rank['absent_parent_paths'])}
assert results['original']['object_sha256']==results['independent']['object_sha256'] and results['original']['log_sha256']==results['independent']['log_sha256']
assert before=={str(p.resolve()):H(p) for p in files}
out={'status':'PASS_INDEPENDENT_FREE_J_PELL_INDICES_AUDIT','inputs_sha256':before,'graph_rows':95,'statement_mutations_rejected':len(mutations),'first_norm_conversion_cases':420,'main_delta_conversion_cases':30,'closure_modules':len(seen),'parent_objects':len(tracked),'absent_companions':len(absent),'results':results,'scope':'Bounded historical single-author existence of first and main Pell indices assuming natural ports, internal zero, all inputs positive and beta positive; no index comparison, rank recovery, checker calibration or iPRA theorem.'};path=HERE/'receipt.json'
if path.exists():raise ValueError('refusing receipt overwrite')
path.write_text(json.dumps(out,sort_keys=True,indent=2)+'\n');print(out['status'],H(path))
