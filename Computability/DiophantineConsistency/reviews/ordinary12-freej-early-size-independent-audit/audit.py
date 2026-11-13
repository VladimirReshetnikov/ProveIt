#!/usr/bin/env python3
"""Independent free-J early-size theorem and bounded replay artifact audit."""
import hashlib,json,os,re,subprocess
from pathlib import Path
if not __debug__:raise RuntimeError('independent audit requires assertions enabled')
HERE=Path(__file__).resolve().parent;ROOT=HERE.parents[3];BASE=ROOT/'Computability/DiophantineConsistency';TASK=BASE/'research/ordinary12-ipra-bridge/free-j-early-size-prototype';RANK=TASK.parent/'rank-adapter-prototype';FREEJ=TASK.parent/'free-j-prototype';GRAPH=BASE/'con-zfc-diophantine-forms/115-synchronized-exponents/supplement/circuits/positive12_95_degree70.json';ORIG=Path('/tmp/ipra-ordinary12-early-size-replay-01');FRESH=Path('/tmp/ipra-freej-early-size-independent-replay-02');FRESH_RECEIPT=Path('/tmp/ipra-freej-early-size-independent-replay-02-receipt.json');PARENT=Path('/tmp/ipra-aq29-fresh-project-pair');SNAP=Path('/tmp/ipra-aq29-fresh-source-closure-v2');PROVIDER=Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/build-all-receipt.json');PACKAGE=Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib');LEAN=Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean');PA=BASE/'reviews/fresh-project-pair-independent-audit';RA=BASE/'reviews/ordinary12-rank-adapter-independent-audit';FA=BASE/'reviews/ordinary12-freej-prototype-independent-audit';MA=BASE/'reviews/manuscript115-reconstruction-independent-audit'
H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest();J=lambda p:json.loads(Path(p).read_text());RAW=lambda s:hashlib.sha256(s.encode()).hexdigest()
files=[Path(__file__),TASK/'FreeJEarlySize.lean',TASK/'replay.py',TASK/'replay-receipt.json',TASK/'README.md',RANK/'Ordinary12RankAdapter.lean',RANK/'replay.py',FREEJ/'Ordinary12FreeJ.lean',GRAPH,FRESH_RECEIPT,PARENT/'pair-state.json',PARENT/'author/state.json',SNAP/'manifest.json',PROVIDER,LEAN,PA/'receipt.json',PA/'terminal-observation.json',RA/'receipt.json',RA/'terminal-observation.json',FA/'receipt.json',FA/'terminal-observation.json',MA/'receipt.json',MA/'terminal-observation.json']
before={str(p.resolve()):H(p) for p in files};assert H(TASK/'FreeJEarlySize.lean')=='0e670e6d0cd8431893b5ccf3267d9857eb8d7301af0acb49acb04433e07c44fb' and H(TASK/'replay-receipt.json')=='a8d63f37e23973b148db16b6eedc3c6a88b0d15ef248d6db14608d142867b865' and H(FRESH_RECEIPT)=='e90bfe600e229e341efc18d736739c201dde92d11c050aca62fc21e008f64344'
for f in (TASK/'FreeJEarlySize.lean',TASK/'replay.py',TASK/'replay-receipt.json',TASK/'README.md'):
 assert hashlib.sha256(subprocess.check_output(['git','show','dfd7453b62:'+str(f.relative_to(ROOT))],cwd=ROOT)).hexdigest()==H(f)
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
pell=BASE/'reviews/ordinary12-freej-pell-indices-independent-audit';assert H(pell/'receipt.json')=='c09579e066a478584a5d8b8997b147b538959c41fc3a474fa1abade552bdfe68' and J(pell/'terminal-observation.json')['audit_observed_exit_code']==0
win=BASE/'reviews/ordinary12-freej-early-window-independent-audit';assert H(win/'receipt.json')=='20161d494fccd5e8199a2adc4ae444656f6601eb53bc9c62e1e8f83113160b5d' and J(win/'terminal-observation.json')['audit_observed_exit_code']==0
earlyaudit=BASE/'reviews/ordinary12-freej-early-index-independent-audit';assert H(earlyaudit/'receipt.json')=='1113400bc18dff719cf0b8f3b4f53a85fbea9b7b88c2406fa5f4371cd1b29055' and J(earlyaudit/'terminal-observation.json')['audit_observed_exit_code']==0
compaudit=BASE/'reviews/ordinary12-freej-index-comparison-independent-audit';assert H(compaudit/'receipt.json')=='2a722d0603bc9c2d7968cbce5166f0ba3555493f2ce098547c9182fc63b8f63b' and J(compaudit/'terminal-observation.json')['audit_observed_exit_code']==0
source=(TASK/'FreeJEarlySize.lean').read_text()
assert 'variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]' in source
def validate(s):
 head=' '.join(s.split('theorem early_size',1)[1].split(':= by',1)[0].split())
 want='(p : Fin 4 → ℕ) (v : Fin 12 → V) (hb : 0<(p 0:V)) (hl : (p 2:V)<(p 0:V)) (hh : (p 3:V)<2*(p 0:V)) (hv : ∀ j,0<v j) (hz : InternalZero (literal (fun j => (p j:ℤ))) v) : let q : V := 1+v 0*(p 0:V) let R : V := ((q-1)*(q-v 1)+v 2)*(q^2-1)+((p 2:V)+q*(p 3:V))*v 0 let k : V := v 8+v 9 let c : V := v 8+v 6*k let a : V := v 5*v 6+v 6 (a+2)*delta a*delta a<c ∧ 2*R<c'
 if head!=want:raise ValueError('wrong theorem statement')
 for x in ['comparison p v hb hl hh hv hz','rw [←hmy]','large_of_six _ m hm6']:
  if x not in s:raise ValueError(('missing proof call',x))
validate(source)
mutations=[('(p 2:V)<(p 0:V)','(p 2:V)≤(p 0:V)'),('(p 3:V)<2*(p 0:V)','(p 3:V)<3*(p 0:V)'),('∀ j,0<v j','∀ j,0≤v j'),('delta a*delta a<c','delta a*delta a≤c'),('2*R<c','2*R≤c')]
for a,b in mutations:
 assert a in source
 try:validate(source.replace(a,b))
 except ValueError:pass
 else:raise AssertionError(('mutation accepted',a))
def coords(base,n):
 x,y=1,0
 for _ in range(n):x,y=(base+2)*x+(base+1)*(base+3)*y,x+(base+2)*y
 return x,y
for a in range(15):
 for m in range(6,11):assert (a+2)*((a+1)*(a+3))**2<coords(a,m)[1]
assert (0+2)*((0+1)*(0+3))**2>=coords(0,1)[1]
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
integral=SNAP/'src/DiophantineConsistency/ArithmeticPellIntegralSolution.lean';assert H(integral)=='c07a7cf5afc0f753191010fd2b51d251c85ba4375dfa5c6b124f9851d158cea0' and 'DiophantineConsistency.ArithmeticPellIntegralSolution' in seen
head=' '.join(integral.read_text().split('theorem integral_solution_tsub',1)[1].split(':= by',1)[0].split())
assert head=='(a c p i f : V) (hp : 0<p) (hi : 0<i) (hf : 0<f) (hcp : c=ycoord p a) (hnorm : (i*c*c)*(i*c*c)=delta a*(f*f-1)) (hbig : (a+2)*delta a*delta a<c) : ∃ m : V, 0<m ∧ p∣m ∧ f=xcoord m a ∧ i*c*c=delta a*ycoord m a'
rx=re.compile(r"^'([^']+)' depends on axioms: \[([^\]]*)\]",re.M|re.S);results={}
for label,out,receipt,pin in [('original',ORIG,TASK/'replay-receipt.json','a8d63f37e23973b148db16b6eedc3c6a88b0d15ef248d6db14608d142867b865'),('independent',FRESH,FRESH_RECEIPT,'e90bfe600e229e341efc18d736739c201dde92d11c050aca62fc21e008f64344')]:
 d=J(receipt);assert H(receipt)==pin and d['status']=='PASS_BOUNDED_FREEJ_EARLY_SIZE' and d['inner_exit_code']==d['lean_exit_code']==d['deps_exit_code']==0
 comp=J(out/'comparison-receipt.json');assert H(out/'comparison-receipt.json')==d['inner_receipt_sha256'] and comp==d['inner_receipt'] and comp['status']=='PASS_BOUNDED_FREEJ_INDEX_COMPARISON'
 early=comp['inner_receipt'];pelldata=early['inner_receipt'];main=pelldata['inner_receipt'];transport=main['inner_receipt'];first=transport['inner_receipt'];rank=first['inner_receipt']
 for dat,status in [(early,'PASS_BOUNDED_FREEJ_EARLY_INDEX'),(pelldata,'PASS_BOUNDED_FREEJ_PELL_INDICES'),(main,'PASS_BOUNDED_FREEJ_MAIN_RANK_CONGRUENCE'),(transport,'PASS_BOUNDED_FREEJ_FIRST_TRANSPORT'),(first,'PASS_BOUNDED_FREEJ_FIRST_DIVISIBILITY'),(rank,'PASS_BOUNDED_CONDITIONAL_FREEJ_RANK_ADAPTER')]:assert dat['status']==status
 for f,expected in [('comparison/early-receipt.json',comp['inner_receipt_sha256']),('comparison/early/pell-receipt.json',early['inner_receipt_sha256']),('comparison/early/pell/rank-receipt.json',pelldata['inner_receipt_sha256']),('comparison/early/pell/rank/rank-receipt.json',main['inner_receipt_sha256']),('comparison/early/pell/rank/rank/rank-receipt.json',transport['inner_receipt_sha256']),('comparison/early/pell/rank/rank/rank/rank-receipt.json',first['inner_receipt_sha256'])]:assert H(out/f)==expected
 assert set(rank['source_closure'])==seen and set(rank['absent_parent_paths'])==absent and {x['source'] for x in rank['seed_links'].values()}==set(tracked)
 lib=out/'comparison/early/pell/rank/rank/rank/rank/freej/concrete/composed/base/lib';module=lib/'DiophantineConsistency'
 for link,meta in rank['seed_links'].items():
  q=Path(link);src=Path(meta['source']);assert q==(lib/src.relative_to(PARENT/'author/lib')) and q.is_symlink() and q.resolve()==src.resolve() and H(q)==meta['sha256']==tracked[str(src)]
 assert all(not os.path.lexists(x) for x in absent)
 expected_gen={'FreeJEarlyIndex':'932432ae53f76593ba4a9822a3e4cd8a5b2a9b4e6a7f17acdcc17287a0a732f3','FreeJEarlyWindow':'07195c1a37ef3baaa025ad74a9397bfac2dfd71b242a004e0e3145899fb32c99','FreeJPellIndices':'20b39ea983c17d69b0edc4ab9a0b4239f685c2c250418c04e4c9ae2ad8dc07cb'}
 assert early['generated_objects']==expected_gen
 for name,sha in expected_gen.items():assert H(module/(name+'.olean'))==sha and not (module/(name+'.olean')).is_symlink()
 for name,dat,sha in [('FreeJMainOrientation',main,'62a60121277c2aa71ebc457023dc4315fcf8855f614e89b5814350cc4dcf131c'),('FreeJFirstTransport',transport,'79be848e07657adfb949dcbfe87ff993ee73a957f65713344d374d83540a3df8'),('FreeJRootBinding',first,'58860b9c6f256a15df038991edc682af4b4c831ab0ae3c3565f1f14ea4833b40')]:assert H(module/(name+'.olean'))==dat['object_sha256']==sha
 seed=out/'comparison/FreeJIndexComparison.olean';copy=module/'FreeJIndexComparison.olean';assert H(seed)==H(copy)==d['comparison_seed_sha256']==comp['object_sha256']=='f9d436b819905f88c551d9b299fcaa45c3d3d451c158de1cca31616eaa4a4a8c' and not copy.is_symlink() and (seed.stat().st_dev,seed.stat().st_ino)!=(copy.stat().st_dev,copy.stat().st_ino)
 src=out/'src/DiophantineConsistency/FreeJEarlySize.lean';obj=out/'FreeJEarlySize.olean';assert H(src)==H(TASK/'FreeJEarlySize.lean') and H(obj)==d['object_sha256']=='7c80bb95c1287441c9e171b2ec8c4a9feaa5e028d9143748061896582eea9841' and not obj.is_symlink()
 log=d['lean_stdout']+d['lean_stderr'];reports=rx.findall(log);assert [n for n,_ in reports]==['FreeJEarlySize.early_size'] and all({x.strip() for x in v.split(',')}<={'propext','Classical.choice','Quot.sound'} for _,v in reports) and 'sorryAx' not in log and 'warning:' not in log
 env=os.environ.copy()
 for n in ('LEAN_SRC_PATH','LEAN_SYSROOT','LD_LIBRARY_PATH','LD_PRELOAD','LD_AUDIT'):env.pop(n,None)
 env['LEAN_PATH']=str(lib)+':'+str(PACKAGE);deps=subprocess.run([str(LEAN),'--deps',str(src)],env=env,capture_output=True,text=True,timeout=60)
 assert deps.returncode==0 and deps.stdout==d['deps_stdout'] and set(deps.stdout.splitlines())=={str(PACKAGE/'Init.olean'),str(copy),str(module/'ArithmeticPellResidueAux.olean')}
 assert H(PACKAGE/'Init.olean')==parent['guarded_companions'][str(PACKAGE/'Init.olean')]['sha256']
 for path,sha in d['inputs_sha256'].items():assert H(path)==sha
 results[label]={'receipt_sha256':H(receipt),'object_sha256':H(obj),'comparison_object_sha256':H(copy),'linked_objects':len(rank['seed_links']),'absent_companions':len(rank['absent_parent_paths'])}
assert results['original']['object_sha256']==results['independent']['object_sha256'];assert before=={str(p.resolve()):H(p) for p in files}
out={'status':'PASS_INDEPENDENT_FREE_J_EARLY_SIZE_AUDIT','inputs_sha256':before,'graph_rows':95,'statement_mutations_rejected':len(mutations),'recurrence_size_sanity_cases':75,'integral_solution_source_sha256':H(integral),'closure_modules':len(seen),'parent_objects':len(tracked),'absent_companions':len(absent),'results':results,'scope':'Bounded historical early size with model MC and MF assumptions; no strong norm, final rank, fixed-port interpretation, checker calibration or iPRA theorem.'};path=HERE/'receipt.json'
if path.exists():raise ValueError('refusing receipt overwrite')
path.write_text(json.dumps(out,sort_keys=True,indent=2)+'\n');print(out['status'],H(path))
