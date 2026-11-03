#!/usr/bin/env python3
"""Guarded post-425 direct90 adapter join with actual project-header scans.

The caller must provide the immutable final stage-425 receipt and its digest,
plus the digest of the separately captured final overlay comparison. All outputs
are fresh; any failure is retained. Package-transitive and dynamic ancestry are
not authenticated by this runner.
"""
from pathlib import Path
from hashlib import sha256
import argparse, json, os, re, shutil, subprocess, sys, tempfile, time, traceback
if sys.flags.optimize: raise SystemExit('optimized Python refused')
H=Path(__file__).resolve().parent; D=H.parents[1]; ROOT=D.parents[1]
B=D/'research/ordinary12-ipra-bridge'
LIB=Path('/tmp/compact12-ipra-expanded-coherent-20261102/lib')
PACKAGE=Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib')
LEAN=Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean')
HELPER=B/'compact12-ipra-all-project-import-inventory/ReadObjectImports.lean'
INVENTORY=B/'compact12-ipra-all-project-import-inventory/observations/attempt01/result.json'
CONE=B/'compact12-ipra-expanded-cone-rebuild-stage317-source-retry/cone-repinned.json'
ADAPTER=H/'observations/adapter-preflight01/result.json'
PLAN=D/'research/ordinary12-direct-main-probe/ipra-join-source-plan.json'
FINAL=D/'reviews/ordinary12-direct-main-ipra-import-preflight/observations/final01/result.json'
SCAN=D/'reviews/ordinary12-direct-main-ipra-import-preflight/observations/attempt01/result.json'
OVERLAY=D/'reviews/ordinary12-direct-main-ipra-import-preflight/observations/overlay01/result.json'
ORIGINAL_CONE=B/'compact12-ipra-expanded-cone-preflight/result-v2.json'
APPROVED_CONE=B/'compact12-ipra-expanded-cone-rebuild-stage419-source-retry/cone-repinned.json'
QSCHEMA_RECEIPT=B/'compact12-ipra-expanded-cone-rebuild-stage419-source-retry/observations/batch-084/stage-0419/terminal.json'
QSCHEMA_FAILED=B/'compact12-ipra-expanded-cone-rebuild-stage419/observations/batch-084/stage-0419/terminal.json'
QSCHEMA_FAILED_LOG=QSCHEMA_FAILED.parent/'compile.log'
QSCHEMA_REVIEW=D/'reviews/compact12-stage419-qschema-independent/observations/attempt01/terminal.json'
QSCHEMA_REVIEW_SCRIPT=D/'reviews/compact12-stage419-qschema-independent/check.py'
QSCHEMA_REVIEW_STDOUT=QSCHEMA_REVIEW.parent/'stdout'
QSCHEMA_REVIEW_STDERR=QSCHEMA_REVIEW.parent/'stderr'
STANDARD_WARNING_VERIFY=H/'verify-standard-warning.py'
STANDARD_WARNING_EXPECTED=H/'expected-standard-warning.txt'
STANDARD_WARNING_MUTATIONS=H/'observations/standard-warning-mutations01/terminal.json'
STANDARD_WARNING_MUTATION_SCRIPT=H/'check-standard-warning-policy.py'
PINS={LEAN:'e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550',
 HELPER:'886d46d27a94d512e47c4fe571654e4a432ab536f995b52bd1300324678fc10f',
 INVENTORY:'bf812db57d68117d47d3df792e4a0d6879019d442c4f0f2b0fbef8b861f363f2',
 CONE:'eb5a8a3c8efb7b1d936d4c77ba2c6d201aff6d03f23c9e1697dd2b518aefcbf2',
 SCAN:'01c68aaea9e3548f25589694cbb0c4582f66c0fce7b072ba0d3a3765fec950a1',
 OVERLAY:'385173546dacd65f2c441c8ed2fd0dfd2086e0a59b2f14a98fbc9a0c4ca1eeae',
 ORIGINAL_CONE:'35fce2dd6720ca1f2db8c39e42ad099f5653bf6b12939fcb77db3fd0fa252ed4',
 PLAN:'1bd45fb3cfc1f3a3bc9af12acc9098efc9b2a53aa3ee0f6952c0510d396f1c71',
 ADAPTER:'59438b2bbd2136e156b7c9d51e5d0caea747c1e7c974e86068072f742bd6f2a3',
 H/'adapter-preflight.py':'cda424091532f8491ac65205c47a1007fcaf7a84bfdc3f5afc4bcda5f7773961'}
PINS.update({
 APPROVED_CONE:'b5eb6a00e30599c49a851b38746582c75f1eaba2e6c9a66ed6a8adec9f4dc424',
 QSCHEMA_RECEIPT:'217c73fc4c9f82c75351021ca070c456e4e7b60b25b03e77973869237e5b7407',
 QSCHEMA_FAILED:'e767354a4e1bc253cb0dde92ea4a72d5ef1fb42f2d4a2f73c6797047510e941f',
 QSCHEMA_FAILED_LOG:'028258a888e8d7c81c61b543c5a6a888988ceb6fcf51bd41b874c1b8213d2b6d',
 QSCHEMA_REVIEW:'873e08cf380047ba3c0f3560c3952ddf8fc3f4c89a58ce34d8764f5de50b1825',
 QSCHEMA_REVIEW_SCRIPT:'ba33da5e0aa0e40261aa8a6e9d993b0872d822d4dcc102609fe51978f61c510a',
 QSCHEMA_REVIEW_STDOUT:'15ba930992f18a071102e2a0d0d7a2667087fdf73300cdf0d27fae0244d11aa8',
 QSCHEMA_REVIEW_STDERR:'e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855'})
PINS.update({
 STANDARD_WARNING_VERIFY:'225e368ddc1350f4db7a03fd5ce84693b7a53a0d89330ef0e338c8b9e12e4a93',
 STANDARD_WARNING_EXPECTED:'97d21d17b2e82cd1f87c74a35b3bb9e8fd98d610e6cb33b7f8e1cf1faab59006',
 STANDARD_WARNING_MUTATIONS:'6bc0681058f0662161ea4552c42dd026d958a4ee35eda9915d7dec4990c37b6f',
 STANDARD_WARNING_MUTATION_SCRIPT:'eb8edd43f137f88c07a4c640c145d6a17bbf84066e6b5d99e9a815eee3b7e957',
 STANDARD_WARNING_MUTATIONS.parent/'stdout':'425731bc82844937ba11362e4454070cc70b6a4b17e4db5ee68910aaa5044c22',
 STANDARD_WARNING_MUTATIONS.parent/'stderr':'e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855'})
SUFFIXES=('.olean','.olean.private','.olean.server','.ilean','.ir','.olean.hash',
 '.olean.private.hash','.olean.server.hash','.ilean.hash','.ir.hash')
AFFECTED=['DiophantineConsistency.IPRASuccessorInduction','DiophantineConsistency.IPRAAddOneGeneral',
 'DiophantineConsistency.IPRASuccessorInductionConverse','DiophantineConsistency.IPRAStandardTheory']
ADAPTER_SOURCES=[
 ('PositiveModelIPRAAdapter', B/'positive-model-ipra-adapter-prototype/PositiveModelIPRAAdapter.lean','4faabe0a42f1adabe102e58c4355ddbdf03f9c0ccb29498c48c99241066356ea'),
 ('PositiveModelIPRAStandardAdapter', B/'positive-model-ipra-standard-adapter-prototype/PositiveModelIPRAStandardAdapter.lean','7046c2d8fde9411d517641829e3158733bfec14e778fdce6cb7d86cc9f3ccb78'),
 ('PositiveModelIPRAReferenceTranslated', B/'positive-model-ipra-reference-translated-prototype/PositiveModelIPRAReferenceTranslated.lean','5fe36c45884ab0dfa14bce35d8855038915e07885c3add6bdc1b3cb1051fbe66')]
CLIENT=('Direct90IPRAEndpoint',D/'research/ordinary12-direct90-ipra-endpoint-draft/Direct90IPRAEndpoint.lean',
 '613a987b593402233521f2abe38973bc37985565a9a3acc82a5ded1c8d72a28e')
def need(v,m):
 if not v: raise RuntimeError(m)
def sha(p): return sha256(Path(p).read_bytes()).hexdigest()
def diagnostic(text,severity):
 return re.search(r'\b'+re.escape(severity)+r'(?:\([^\n)]*\))?:',text) is not None
def rec(p):
 p=Path(p)
 if not os.path.lexists(p): return None
 need(p.is_file(),'dangling/non-file '+str(p))
 return {'sha256':sha(p),'resolved':str(p.resolve(strict=True)),'link':os.readlink(p) if p.is_symlink() else None}
def resources():
 pids=[]
 for p in Path('/proc').iterdir():
  if not p.name.isdigit():continue
  try: exe=(p/'exe').resolve(strict=True)
  except (OSError,RuntimeError):continue
  if exe==LEAN.resolve(strict=True):pids.append(int(p.name))
 row=next(x for x in Path('/proc/meminfo').read_text().splitlines() if x.startswith('MemAvailable:'))
 return {'time_ns':time.time_ns(),'mem_available_kib':int(row.split()[1]),'lean_pids':sorted(pids)}
def guard_resource():
 r=resources();need(r['mem_available_kib']>=8*1024**2 and len(r['lean_pids'])<2,'resource preflight');return r
def snapshot_lib():
 return {p.relative_to(LIB).as_posix():rec(p) for p in LIB.rglob('*') if p.is_file()}
def relative_module(name):
 need(bool(re.fullmatch(r'[A-Za-z_][A-Za-z0-9_]*(\.[A-Za-z_][A-Za-z0-9_]*)*',name)), 'bad module '+name)
 return name.replace('.','/')
def manifest_recheck(final):
 for n,row in final['records'].items():
  stem=LIB/relative_module(n)
  current={s:rec(str(stem)+s) for s in SUFFIXES}
  need(current==row['overlay'],'canonical drift '+n)
  if row['in_direct']:
   selected=row['selected_provider']; old=Path(selected['path']); osrc=str(old)[:-len('.olean')]
   need(rec(old)==selected['record'],'selected object drift '+n)
   need({s:rec(osrc+s) for s in SUFFIXES}==selected['companions'],'selected companion drift '+n)
   if current['.olean'] is not None:
    for s in SUFFIXES:
     a=current[s];b=selected['companions'][s]
     need((None if a is None else a['sha256'])==(None if b is None else b['sha256']),
          'overlap companion mismatch '+n+s)

def validate_final(final):
 expected_pins={str(p):PINS[p] for p in (SCAN,OVERLAY,ORIGINAL_CONE)}
 need(final['input_pins']==expected_pins and final['overlay_root']==str(LIB),'final input pins/root')
 scan=json.loads(SCAN.read_text())['roots']['DirectMainHalt']
 direct=set(scan['selected_ancestors']);cone=set(json.loads(ORIGINAL_CONE.read_text())['topological_candidate'])
 need(len(direct)==765 and len(cone)==425 and not direct&cone,'final expected module sets')
 need(set(final['records'])==direct|cone,'final record membership')
 missing=[];mismatch=[];absent=[]
 for n,row in final['records'].items():
  need(row['in_direct']==(n in direct) and row['in_cone']==(n in cone),'final membership flag '+n)
  if n in cone and row['overlay']['.olean'] is None:absent.append(n)
  if n in direct:
   need(row['selected_provider']==scan['resolved'][n],'final selected provenance '+n)
   cur=row['overlay']['.olean'];old=row['selected_provider']['record']
   same=cur is not None and cur['sha256']==old['sha256']
   need(row['same_object_sha256']==same,'final comparison flag '+n)
   if cur is None:missing.append(n)
   elif not same:mismatch.append(n)
 report=final['report']
 need(sorted(missing)==report['direct_missing'] and sorted(mismatch)==report['direct_mismatched'] and
      sorted(absent)==report['cone_missing'] and report['direct_matched']==len(direct)-len(missing)-len(mismatch),
      'final report classification')
 need(not report['changed_during_comparison'] and not final['records_before'],'final comparison not stable')
def producer_receipts(cone,final):
 files=list(B.glob('compact12-ipra-expanded-cone-rebuild-*/observations/batch-*/stage-*/terminal.json'))
 files+=list(B.glob('compact12-ipra-expanded-cone-rebuild/observations/batch-*/stage-*/terminal.json'))
 bymod={}
 for p in files:
  try:d=json.loads(p.read_text())
  except (ValueError,OSError):continue
  n=d.get('module')
  if n not in cone['candidate_sources'] or not d.get('success') or d.get('exit_code')!=0:continue
  current=final['records'][n]['overlay']['.olean']; row=cone['candidate_sources'][n]
  if not current or d.get('object_sha256')!=current['sha256'] or d.get('source_sha256')!=row['source_sha256']:continue
  need(d.get('source_unchanged') and d.get('guards_unchanged'),'producer reported drift '+n)
  need(d.get('lean_sha256')==sha(LEAN),'producer Lean mismatch '+n)
  command=d.get('command',[]);source=ROOT/row['canonical_candidates'][0];obj=LIB/(relative_module(n)+'.olean')
  need(len(command)>=5 and command[0]==str(LEAN) and command[-3:]==[str(source),'-o',str(obj)],'producer command mismatch '+n)
  expected_mem='-M6000' if d.get('index')==285 else '-M3000'
  need(command[1:4]==[expected_mem,'-j1','-DElab.async=false'] and command[4].startswith('--root='),
       'producer flags mismatch '+n)
  need(Path(command[4][len('--root='):])/(relative_module(n)+'.lean')==source,'producer source root mismatch '+n)
  need(sha(p.parent/'source.lean')==row['source_sha256'] and sha(source)==row['source_sha256'],'producer source snapshot mismatch '+n)
  log=p.parent/'compile.log';need(sha(log)==d.get('log_sha256'),'producer log mismatch '+n)
  runner=p.parents[3]/'run.py';need(sha(runner)==d.get('runner_sha256'),'producer runner mismatch '+n)
  guards=d.get('guards');need(isinstance(guards,dict) and guards,'missing producer guards '+n)
  deps=p.parent/'deps';deps_stderr=p.parent/'deps.stderr'
  need(deps.is_file() and deps_stderr.is_file() and not deps_stderr.read_bytes(),'producer dependency scan error '+n)
  expected_guards=set()
  for line in deps.read_text().splitlines():
   path=Path(line)
   need(path.is_absolute() and path.suffix=='.olean' and path.is_file(),'invalid producer dependency '+n)
   stem=str(path)[:-len('.olean')]
   expected_guards.update(stem+s for s in SUFFIXES)
  need(set(guards)==expected_guards,'producer dependency guard set mismatch '+n)
  for path,record in guards.items():need(rec(path)==record,'producer dependency guard drift '+n+' '+path)
  text=log.read_text();need(not diagnostic(text,'error') and 'sorryAx' not in text,'producer error diagnostic '+n)
  warning=None
  if d.get('accepted_exact_warning'):
   verify=p.parents[3]/'verify_warning.py';expected=p.parents[3]/'expected-warning.txt'
   need(verify.is_file() and expected.is_file(),'missing warning policy '+n)
   check=subprocess.run([sys.executable,str(verify),str(log)],capture_output=True,text=True,timeout=30)
   need(check.returncode==0 and not check.stderr,'exact warning policy failed '+n)
   warning={'verifier':str(verify),'expected':str(expected),'verifier_sha256':sha(verify),'expected_sha256':sha(expected),
            'stdout_sha256':sha256(check.stdout.encode()).hexdigest()}
  else:need(not diagnostic(text,'warning'),'unaccepted producer warning '+n)
  bymod.setdefault(n,[]).append({'path':str(p),'sha256':sha(p),'index':d.get('index'),
   'object_sha256':d['object_sha256'],'command':command,'log_sha256':sha(log),
   'runner':str(runner),'runner_sha256':sha(runner),'log':str(log),
   'source_snapshot':str(p.parent/'source.lean'),'source_sha256':row['source_sha256'],
   'deps':str(deps),'deps_sha256':sha(deps),'deps_stderr':str(deps_stderr),
   'deps_stderr_sha256':sha(deps_stderr),'guards':guards,'warning_policy':warning})
 need(set(bymod)==set(cone['candidate_sources']),'missing matching successful stage receipts')
 order=cone['topological_candidate']
 for index,n in enumerate(order,1):need(any(x['index']==index for x in bymod[n]),'stage index mismatch '+n)
 return bymod

def monitored(cmd,env,obs,label,limit=180):
 before=guard_resource();samples=[];reason=None;start=time.monotonic()
 out=obs/(label+'.stdout');err=obs/(label+'.stderr')
 with out.open('xb') as so,err.open('xb') as se:
  proc=subprocess.Popen(cmd,stdout=so,stderr=se,env=env)
  try:
   while proc.poll() is None:
    r=resources();samples.append(r)
    if r['mem_available_kib']<8*1024**2 or len(r['lean_pids'])>2:reason='resource guard';break
    if time.monotonic()-start>limit:reason='timeout';break
    time.sleep(1)
  except Exception as exc:reason='monitor exception: '+repr(exc)
  finally:
   if reason and proc.poll() is None:proc.kill()
   proc.wait()
 row={'command':cmd,'preflight':before,'samples':samples,'exit':proc.returncode,'reason':reason,
      'elapsed':time.monotonic()-start,'stdout_sha256':sha(out),'stderr_sha256':sha(err)}
 (obs/(label+'.json')).write_text(json.dumps(row,indent=2,sort_keys=True)+'\n')
 need(proc.returncode==0 and reason is None,'process failed '+label)
 return out.read_text(),err.read_text()

def scan_closure(roots,paths,env,obs,prefix,project_known):
 pending=list(roots);seen={};outside={};batch=0
 def resolve(n):
  rel=relative_module(n)+'.olean'
  for base in paths:
   p=base/rel
   if p.is_file():return p
  p=PACKAGE/rel
  if p.is_file():return ('package',p)
  p=LEAN.parent.parent/'lib/lean'/rel
  if p.is_file():return ('lean_sysroot',p)
  return None
 while pending:
  names=[];resolved={}
  while pending and len(names)<32:
   n=pending.pop()
   if n in seen or n in outside or n in resolved:continue
   p=resolve(n)
   need(p is not None,'unresolved import '+n)
   if isinstance(p,tuple):
    need(n not in project_known,'known project module resolved from package/sysroot '+n)
    stem=str(p[1])[:-len('.olean')]
    outside[n]={'kind':p[0],'path':str(p[1]),'record':rec(p[1]),'companions':{s:rec(stem+s) for s in SUFFIXES}}
    continue
   names.append(n);resolved[n]=p
  if not names:continue
  command=[str(LEAN),'-M3000','-j1','-DElab.async=false','--run',str(HELPER)]+[str(resolved[n]) for n in names]
  stdout,stderr=monitored(command,env,obs,f'{prefix}-headers-{batch:03}',60);batch+=1
  need(not stderr,'header stderr');pathmap={str(v):k for k,v in resolved.items()};cur=None;headers={}
  for line in stdout.splitlines():
   if line.startswith('BEGIN '):
    need(cur is None and line[6:] in pathmap,'header BEGIN');cur=pathmap[line[6:]];need(cur not in headers,'duplicate header');headers[cur]=[]
   elif line.startswith('IMPORT ') and cur is not None:headers[cur].append(line[7:])
   elif line=='END' and cur is not None:cur=None
   else:raise RuntimeError('header parse '+line)
  need(cur is None and set(headers)==set(names),'incomplete headers')
  for n in names:
   p=resolved[n];stem=str(p)[:-len('.olean')]
   seen[n]={'path':str(p),'record':rec(p),'companions':{s:rec(stem+s) for s in SUFFIXES},'imports':headers[n]}
   pending.extend(headers[n])
 need(set(roots)<=set(seen),'requested project root unresolved')
 return {'roots':roots,'project':seen,'outside':outside,'header_batches':batch}

def recheck_outside(closure):
 for n,row in closure['outside'].items():
  path=Path(row['path']);stem=str(path)[:-len('.olean')]
  need(rec(path)==row['record'] and {s:rec(stem+s) for s in SUFFIXES}==row['companions'],
       'package/sysroot object changed '+n)

def recheck_new(stages):
 for row in stages:
  path=Path(row['object']);stem=str(path)[:-len('.olean')]
  need(rec(path)==row['object_record'] and {s:rec(stem+s) for s in SUFFIXES}==row['companions'],
       'new join object/companion changed '+row['module'])
  need(sha(row['compiled_source'])==row['source_sha256'] and sha(row['archived_source'])==row['source_sha256'],
       'copied join source changed '+row['module'])

def main():
 ap=argparse.ArgumentParser();ap.add_argument('--attempt',required=True);ap.add_argument('--completion',required=True,type=Path)
 ap.add_argument('--completion-sha',required=True);ap.add_argument('--final-sha',required=True)
 ap.add_argument('--cone',required=True,type=Path);ap.add_argument('--cone-sha',required=True);a=ap.parse_args()
 need(bool(re.fullmatch(r'attempt[0-9]+',a.attempt)),'attempt name')
 obs=H/'observations'/a.attempt;need(not obs.exists(),'refusing observation overwrite');obs.mkdir(parents=True)
 runner_hash=sha(__file__);(obs/'runner.py').write_bytes(Path(__file__).read_bytes())
 result={'runner_sha256':runner_hash,'status':'FAILED','scope':'actual selected project headers and guarded author join; package-transitive, dynamic and complete source-object ancestry not authenticated'}
 try:
  need(LEAN.is_file() and LIB.is_dir() and PACKAGE.is_dir(),'missing provider/tool')
  need(shutil.disk_usage('/tmp').free>=4*1024**3,'disk guard')
  for p,pin in PINS.items():need(sha(p)==pin,'input pin '+str(p))
  need(sha(FINAL)==a.final_sha and sha(a.completion)==a.completion_sha and sha(a.cone)==a.cone_sha,'final receipt/cone pin')
  need(a.cone.resolve()==APPROVED_CONE.resolve() and a.cone_sha==PINS[APPROVED_CONE],
       'unapproved final cone')
  review=json.loads(QSCHEMA_REVIEW.read_text())
  need(review['exit']==0 and review['script_sha256']==PINS[QSCHEMA_REVIEW_SCRIPT] and
       review['stdout_sha256']==PINS[QSCHEMA_REVIEW_STDOUT] and
       review['stderr_sha256']==PINS[QSCHEMA_REVIEW_STDERR],'QSchema review receipt')
  mutations=json.loads(STANDARD_WARNING_MUTATIONS.read_text())
  need(mutations['exit']==0 and mutations['script_sha256']==PINS[STANDARD_WARNING_MUTATION_SCRIPT] and
       mutations['stdout_sha256']==PINS[STANDARD_WARNING_MUTATIONS.parent/'stdout'] and
       mutations['stderr_sha256']==PINS[STANDARD_WARNING_MUTATIONS.parent/'stderr'],
       'standard warning mutation receipt')
  completion=json.loads(a.completion.read_text());need(completion.get('index')==425 and completion.get('success') and completion.get('exit_code')==0 and completion.get('source_unchanged') and completion.get('guards_unchanged'),'invalid completion receipt')
  final=json.loads(FINAL.read_text());report=final['report']
  validate_final(final)
  need(not report['cone_missing'] and not report['direct_mismatched'] and not report['changed_during_comparison'],'final comparison failed')
  cone=json.loads(a.cone.read_text());oldcone=json.loads(CONE.read_text());inv=json.loads(INVENTORY.read_text());plan=json.loads(PLAN.read_text());adapter=json.loads(ADAPTER.read_text())
  need(cone['topological_candidate']==oldcone['topological_candidate'],'candidate cone order changed')
  need(set(cone['candidate_sources'])==set(oldcone['candidate_sources']),'candidate source membership changed')
  source_diff={n:{'old_paths':oldcone['candidate_sources'][n]['canonical_candidates'],
                  'new_paths':row['canonical_candidates'],
                  'old_sha256':oldcone['candidate_sources'][n]['source_sha256'],
                  'new_sha256':row['source_sha256']}
               for n,row in cone['candidate_sources'].items()
               if row['canonical_candidates']!=oldcone['candidate_sources'][n]['canonical_candidates'] or
                  row['source_sha256']!=oldcone['candidate_sources'][n]['source_sha256']}
  expected_diff={'ZFCinPA.QSchema':{
   'old_paths':['Logic/Interpretability/ZFCinPA/Lean/ZFCinPA/QSchema.lean'],
   'new_paths':['Logic/Interpretability/ZFCinPA/Lean/ZFCinPA/QSchema.lean'],
   'old_sha256':'80c040905d9d0565f17f6cce8d8036549096088fc2a3559d9c7f6f752b8caa0a',
   'new_sha256':'0a8ffaa78ef63fe51f4b9c35ddea5ee28908204a4e4a06376b43c285c88ca0c1'}}
  need(source_diff==expected_diff,'unapproved corrected-cone source difference: '+str(source_diff))
  normalized=json.loads(json.dumps(cone));correction=normalized.pop('stage419_source_correction')
  need(correction=={'edit':'inline the consistency transfer proof',
   'failed_log_sha256':PINS[QSCHEMA_FAILED_LOG],'failed_terminal_sha256':PINS[QSCHEMA_FAILED],
   'module':'ZFCinPA.QSchema','new_sha256':expected_diff['ZFCinPA.QSchema']['new_sha256'],
   'old_cone_sha256':PINS[CONE],'old_sha256':expected_diff['ZFCinPA.QSchema']['old_sha256']},
   'QSchema correction metadata')
  normalized['candidate_sources']['ZFCinPA.QSchema']['source_sha256']=expected_diff['ZFCinPA.QSchema']['old_sha256']
  normalized['candidate_sources']['ZFCinPA.QSchema']['source_bytes']=10989
  need(normalized==oldcone,'other corrected-cone metadata changed')
  need(len(cone['candidate_sources'])==425 and len(plan['modules'])==23,'unexpected cone/source plan')
  for n,row in cone['candidate_sources'].items():need(sha(ROOT/row['canonical_candidates'][0])==row['source_sha256'],'cone source drift '+n)
  expected_corrections={'BusyBeaver.ZFC.L2Root254':'fee84717177d6575f576ae3e09a3a034071f02422b7a5ef8d9d68e7822864d10',
   'ZFCinPA.NativeSchema':'d6042135723adce366def247894e63cd3ad5d05d1dc57256718e6c82100f3210',
   'ZFCinPA.LSchema':'c68dbfb6e9b152ab71654de3a2b2cf3559ebe1f8e616edabd12e24209ea568f2'}
  for n,h in expected_corrections.items():need(cone['candidate_sources'][n]['source_sha256']==h,'corrected source mismatch '+n)
  for row in plan['modules']:need(sha(D/row['source'])==row['sha256'],'direct source drift '+row['name'])
  for _,p,h in ADAPTER_SOURCES+[CLIENT]:need(sha(p)==h,'adapter/client source drift '+str(p))
  manifest_recheck(final);base_before=snapshot_lib();receipts=producer_receipts(cone,final)
  need(any(Path(x['path']).resolve()==QSCHEMA_RECEIPT.resolve() and
           x['sha256']==PINS[QSCHEMA_RECEIPT] and x['index']==419
           for x in receipts['ZFCinPA.QSchema']),'repaired QSchema producer receipt not selected')
  need(completion['module']==cone['topological_candidate'][-1] and completion['object_sha256']==final['records'][completion['module']]['overlay']['.olean']['sha256'],'completion object mismatch')
  need(any(Path(x['path']).resolve()==a.completion.resolve() and x['sha256']==a.completion_sha and x['index']==425
           for x in receipts[completion['module']]),'completion receipt is not a validated final producer')
  result.update({'completion_path':str(a.completion),'completion_sha256':a.completion_sha,'final_sha256':a.final_sha,
   'cone_path':str(a.cone),'cone_sha256':a.cone_sha,'source_plan_sha256':sha(PLAN),'adapter_preflight_sha256':sha(ADAPTER),'producer_receipts':receipts,
   'corrected_cone_source_diff':source_diff,
   'canonical_inventory_count':len(base_before),'canonical_inventory_sha256':sha256(json.dumps(base_before,sort_keys=True).encode()).hexdigest()})
  tmp=Path(tempfile.mkdtemp(prefix='direct90-ipra-join-'));src=tmp/'src';out=tmp/'lib';src.mkdir();out.mkdir()
  result['output_root']=str(tmp);missing=report['direct_missing'];need(len(missing)==65,'unexpected missing direct set')
  # Lean resolves namespaced modules through the first namespace directory.
  # Materialize one complete fresh union instead of relying on fallback from
  # a partially populated DiophantineConsistency directory.
  for rel,item in base_before.items():
   dst=out/rel;dst.parent.mkdir(parents=True,exist_ok=True)
   need(not os.path.lexists(dst),'duplicate canonical union path '+rel)
   os.symlink(item['resolved'],dst)
  for n in missing:
   row=final['records'][n];need(row['in_direct'] and row['overlay']['.olean'] is None,'bad supplemental module')
   dst=out/relative_module(n);dst.parent.mkdir(parents=True,exist_ok=True)
   for s,item in row['selected_provider']['companions'].items():
    if item is not None:
     need(not os.path.lexists(str(dst)+s),'supplemental union collision '+n+s)
     os.symlink(item['resolved'],str(dst)+s)
  result['supplemental_modules']=missing
  def snapshot_union():
   return {p.relative_to(out).as_posix():rec(p) for p in out.rglob('*') if p.is_file()}
  union_expected=snapshot_union()
  result['initial_union_count']=len(union_expected)
  result['initial_union_sha256']=sha256(json.dumps(union_expected,sort_keys=True).encode()).hexdigest()
  env={'PATH':'/usr/bin:/bin','LEAN_PATH':f'{out}:{PACKAGE}','LEAN_NUM_THREADS':'1'}
  paths=[out]
  roots=['DirectMainHalt','DiophantineConsistency.IPRAExpressionNative','DiophantineConsistency.HAExpressionAssembly',
   'DiophantineConsistency.IPRAStandardTheory','DiophantineConsistency.IPRAReferenceInductionConversion','DiophantineConsistency.AdaptiveEquationSyntax2011']
  project_known=set(inv['objects'])|set(final['records'])|set(AFFECTED)|{x[0] for x in ADAPTER_SOURCES+[CLIENT]}
  pre=scan_closure(roots,paths,env,obs,'pre',project_known);graph={n:x['imports'] for n,x in pre['project'].items()}
  cone_names=set(cone['topological_candidate']);affected=set(graph)&cone_names
  while True:
   nxt=affected|{n for n,xs in graph.items() if any(x in affected for x in xs)}
   if nxt==affected:break
   affected=nxt
  # Direct root is known to be disjoint; adapter impact outside the cone must be exactly four.
  need(affected-cone_names==set(AFFECTED),'new affected modules require analysis: '+str(sorted(affected-cone_names)))
  need(not ({'FreeJRootBinding','FreeJSignedTransport'}&set(graph)),'top-level namespace collision')
  for n,row in pre['project'].items():
   if n not in cone_names and n not in final['records']:
    need(n in inv['objects'] and row['record']['sha256']==inv['objects'][n]['sha256'],'unverified project object '+n)
  result['pre_headers']=pre
  prehash=sha256(json.dumps(pre,sort_keys=True).encode()).hexdigest();result['pre_headers_sha256']=prehash
  # Rebuild all four affected standard modules, then generic adapters, then client.
  byname={row['module']:row for row in adapter['rebuild_order']};need(list(byname)==AFFECTED,'affected order drift')
  stages=[(n,ROOT/byname[n]['source'],byname[n]['source_sha256']) for n in AFFECTED]+ADAPTER_SOURCES+[CLIENT]
  result['stages']=[]
  for i,(n,source,pin) in enumerate(stages,1):
   recheck_new(result['stages'])
   need(snapshot_union()==union_expected,'fresh union changed before stage '+n)
   need(sha(source)==pin,'stage source drift '+n)
   rel=relative_module(n);sp=src/(rel+'.lean');op=out/(rel+'.olean');sp.parent.mkdir(parents=True,exist_ok=True);op.parent.mkdir(parents=True,exist_ok=True)
   # Only the four affected historical objects may be replaced, and only by
   # unlinking fresh union symlinks; never write through to the canonical lib.
   for suffix in SUFFIXES:
    old=Path(str(out/rel)+suffix);key=old.relative_to(out).as_posix()
    if os.path.lexists(old):
     need(n in AFFECTED and old.is_symlink() and rec(old)==union_expected.get(key),
          'unexpected existing join output '+n+suffix)
     old.unlink();union_expected.pop(key)
   shutil.copyfile(source,sp);shutil.copyfile(source,obs/(f'stage-{i:02}.source.lean'));need(sha(sp)==pin,'source copy drift')
   command=[str(LEAN),'-M3000','-j1','-DElab.async=false',f'--root={src}',str(sp),'-o',str(op)]
   stdout,stderr=monitored(command,env,obs,f'stage-{i:02}',180)
   need(sha(sp)==pin and sha(obs/(f'stage-{i:02}.source.lean'))==pin,'stage copied source changed '+n)
   need(op.is_file() and not diagnostic(stdout+stderr,'error') and 'sorryAx' not in stdout+stderr,'stage diagnostics '+n)
   warning=None
   if n=='DiophantineConsistency.IPRAStandardTheory':
    need(not stderr,'standard warning stderr')
    log=obs/(f'stage-{i:02}.stdout')
    check=subprocess.run([sys.executable,str(STANDARD_WARNING_VERIFY),str(log),str(sp)],
                         capture_output=True,text=True,timeout=30)
    need(check.returncode==0 and not check.stderr,'standard exact-warning policy')
    warning={'verifier_sha256':sha(STANDARD_WARNING_VERIFY),'expected_sha256':sha(STANDARD_WARNING_EXPECTED),
             'stdout_sha256':sha256(check.stdout.encode()).hexdigest(),'accepted_exact_warning':True}
   else:
    need(not diagnostic(stdout+stderr,'warning'),'unaccepted stage warning '+n)
   if n=='Direct90IPRAEndpoint':
    theorem_names=['positive_bridge','byte_positive_bridge','standard_consistency','standard_translated_consistency',
                   'reference_consistency','reference_translated_consistency']
    reports={}
    for name in theorem_names:
     q=re.escape('Direct90IPRAEndpoint.'+name)
     matches=re.findall(r"^'"+q+r"' depends on axioms: \[([^\]]*)\]$",stdout,re.M)
     empty=re.findall(r"^'"+q+r"' does not depend on any axioms$",stdout,re.M)
     need(len(matches)+len(empty)==1,'missing or duplicate axiom report '+name)
     axioms=[] if empty else [x.strip() for x in matches[0].split(',') if x.strip()]
     need(set(axioms)<=set(['propext','Classical.choice','Quot.sound']),'unexpected axiom '+name+': '+str(axioms))
     reports[name]=axioms
    result['endpoint_axioms']=reports
   stem=str(op)[:-len('.olean')]
   result['stages'].append({'module':n,'source_sha256':pin,'compiled_source':str(sp),
                            'archived_source':str(obs/(f'stage-{i:02}.source.lean')),
                            'object_sha256':sha(op),'object':str(op),
                            'warning_policy':warning,
                            'object_record':rec(op),'companions':{s:rec(stem+s) for s in SUFFIXES}})
   for suffix,item in result['stages'][-1]['companions'].items():
    if item is not None:union_expected[(rel+suffix)]=item
   recheck_new(result['stages'])
   need(snapshot_union()==union_expected,'fresh union changed after stage '+n)
   manifest_recheck(final);need(snapshot_lib()==base_before,'canonical library changed');recheck_outside(pre)
   for rows in receipts.values():
    for receipt in rows:
     for path,record in receipt['guards'].items():need(rec(path)==record,'producer guard changed '+path)
  post=scan_closure(['Direct90IPRAEndpoint'],paths,env,obs,'post',project_known);result['post_headers']=post
  recheck_new(result['stages'])
  need(snapshot_union()==union_expected,'fresh union changed after post scan')
  recheck_outside(pre);recheck_outside(post)
  for n,row in post['outside'].items():
   need(n in pre['outside'] and row==pre['outside'][n],'new or changed package/sysroot import '+n)
  for n in AFFECTED:
   need(n in post['project'] and post['project'][n]['path']==str(out/(relative_module(n)+'.olean')),'historical affected object selected '+n)
  need(not ({'FreeJRootBinding','FreeJSignedTransport'}&set(post['project'])),'top-level namespace collision')
  for n,row in post['project'].items():
   if n in [x[0] for x in stages]:
    stage=next(x for x in result['stages'] if x['module']==n)
    need(row['record']==stage['object_record'] and row['companions']==stage['companions'],
         'new object/companion mismatch '+n)
   elif n not in cone_names and n not in final['records']:
    need(n in inv['objects'] and row['record']['sha256']==inv['objects'][n]['sha256'],'unverified post object '+n)
  need(snapshot_lib()==base_before,'canonical library changed');manifest_recheck(final)
  for p,pin in PINS.items():need(sha(p)==pin,'input changed '+str(p))
  for n,row in cone['candidate_sources'].items():need(sha(ROOT/row['canonical_candidates'][0])==row['source_sha256'],'cone source changed '+n)
  for row in plan['modules']:need(sha(D/row['source'])==row['sha256'],'direct source changed '+row['name'])
  for n,source,pin in stages:need(sha(source)==pin,'join source changed '+n)
  standard=next(x for x in result['stages'] if x['module']=='DiophantineConsistency.IPRAStandardTheory')
  check=subprocess.run([sys.executable,str(STANDARD_WARNING_VERIFY),str(obs/'stage-04.stdout'),
                       str(src/'DiophantineConsistency/IPRAStandardTheory.lean')],
                       capture_output=True,text=True,timeout=30)
  need(check.returncode==0 and not check.stderr and
       sha256(check.stdout.encode()).hexdigest()==standard['warning_policy']['stdout_sha256'],
       'standard warning policy changed')
  for rows in receipts.values():
   for row in rows:
    need(sha(row['path'])==row['sha256'] and sha(row['runner'])==row['runner_sha256'] and
         sha(row['log'])==row['log_sha256'] and sha(row['source_snapshot'])==row['source_sha256'] and
         sha(row['deps'])==row['deps_sha256'] and sha(row['deps_stderr'])==row['deps_stderr_sha256'],
         'stage receipt/input changed')
    if row['warning_policy']:
     w=row['warning_policy']
     need(sha(w['verifier'])==w['verifier_sha256'] and sha(w['expected'])==w['expected_sha256'],
          'warning policy changed')
     check=subprocess.run([sys.executable,w['verifier'],row['log']],capture_output=True,text=True,timeout=30)
     need(check.returncode==0 and not check.stderr and sha256(check.stdout.encode()).hexdigest()==w['stdout_sha256'],
          'warning baseline changed')
  need(sha(__file__)==runner_hash,'runner changed')
  need(sha(FINAL)==a.final_sha and sha(a.completion)==a.completion_sha and sha(a.cone)==a.cone_sha,'receipt/cone changed')
  result['status']='PASS';result['post_headers_sha256']=sha256(json.dumps(post,sort_keys=True).encode()).hexdigest()
 except Exception as exc:
  result['error']=repr(exc);result['traceback']=traceback.format_exc()
 (obs/'result.json').write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
 print(json.dumps({'status':result['status'],'error':result.get('error'),'output_root':result.get('output_root')}))
 if result['status']!='PASS':raise SystemExit(1)
if __name__=='__main__':main()
