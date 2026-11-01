#!/usr/bin/env python3
"""Focused paired replay; direct companions are pinned, inherited ancestry is explicit."""
from pathlib import Path
import hashlib,json,os,re,shutil,subprocess,tempfile
D=Path(__file__).resolve().parent; R=D.parents[3]; M=D/'manifest.json'
P=Path('/tmp/ipra-quartic-model-peer-21mh4fzd'); PR=R/'Computability/DiophantineConsistency/reviews/ipra-quartic-native-generic-replay/receipt.json'
PREV=PR.parent; OBS=PREV/'terminal-observation.json'; AUD=R/'Computability/DiophantineConsistency/reviews/ipra-quartic-native-generic-audit/receipt.json'
L=Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean'); PKG=Path('/tmp/pra14-full-transitive-2x6o__to/package-lib'); TOOL=L.parent.parent/'lib/lean'
S=('.olean','.olean.private','.olean.server','.ir','.ilean','.olean.hash','.olean.private.hash','.olean.server.hash','.ir.hash','.ilean.hash')
def h(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def scan(stem):
 out={}
 for suffix in S:
  p=Path(str(stem)+suffix)
  if os.path.lexists(p):
   assert p.is_file(),('bad companion',str(p));out[str(p)]={'realpath':str(p.resolve()),'sha256':h(p)}
  else:out[str(p)]=None
 return out
def audit(guards):
 for name,rec in guards.items():
  p=Path(name)
  if rec is None:assert not os.path.lexists(p),('new companion',name)
  else:assert p.is_file() and str(p.resolve())==rec['realpath'] and h(p)==rec['sha256'],('changed companion',name)
def warnings(text):
 tests=[('unused_simp',r'^This simp argument is unused:'),('unused_section',r'^automatically included section variable\(s\) unused in theorem '),('unused_variable',r'^Variable name `[^`]+` is not explicitly referenced\.$'),('simp_suggestion',r"^(?:try 'simp' instead of 'simpa'|Try `simp at this` instead of `simpa using this`)$"),('noop_tactic',r"^'.+' tactic does nothing$"),('unreachable_tactic',r'^this tactic is never executed$'),('deprecation',r'^`[^`]+` has been deprecated(?:[.:].*)?$'),('simp_discrimination',r'^Left-hand side of simp theorem is headed by a `\.other` key in the discrimination tree'),('tactic_sequence',r'^Used `tac1 <;> tac2` where `\(tac1; tac2\)` would suffice$'),('exponent_threshold_notice',r'^exponent [0-9]+ exceeds the threshold [0-9]+, exponentiation operation was not evaluated, use `set_option exponentiation.threshold <num>` to set a new threshold$')]
 out=[]
 for line in text.splitlines():
  if 'warning:' in line:
   msg=line.split('warning:',1)[1].strip(); matches=[k for k,pat in tests if re.search(pat,msg)];assert len(matches)==1,('unrecognized warning',line);out.append({'category':matches[0],'message':msg,'line':line})
 return out
assert h(M)=='f954df6d2bc66e00124b5d410b57470ad197c776f5d23aea1e849f137195c551'
manifest=json.loads(M.read_text()); assert manifest['status']=='FROZEN_FOCUSED_INPUT' and len(manifest['order'])==2 and len(set(manifest['order']))==2
receipt=json.loads(PR.read_text());assert receipt['status']=='MATCHED_PASS' and receipt['runs'][1]['run']==str(P)
assert h(PR)==manifest['parent_receipt_sha256']=='dcbd9c93e8a09470a55f656f0e4c41b35262ff0a80b5114dc9e402c07229e538'
assert h(OBS)==manifest['parent_observation_sha256']=='afba1ebe7f46fcd6fc9c0127bd650ddb57160877ad44748c5380e1e8f69e4072'
ob=json.loads(OBS.read_text()); assert ob['tool_session']==8306 and ob['observed_exit_code']==0 and ob['observed_stdout']=='MATCHED_PASS 18 rows'
ar=json.loads(AUD.read_text()); assert ar['status']=='PASS_FOCUSED_RECEIPT_AUDIT'
for path,digest in ar['input_sha256'].items():assert h(path)==digest,('prior audit input changed',path)
assert ar['input_sha256'][str(PR)]==h(PR)
assert len(receipt['runs'][1]['rows'])==18
def audit_previous():
 for row in receipt['runs'][1]['rows']:
  assert h(P/'lib'/(row['module'].replace('.','/')+'.olean'))==row['object_sha256']
  assert h(PREV/'peer/logs'/(row['module'].replace('.','_')+'.log'))==row['log_sha256']
 audit(receipt['parent_output_guards']);audit(receipt['fallback_guards']);audit(receipt['runs'][1]['guards'])
audit_previous()
prior=json.loads((PREV/'manifest.json').read_text())
retained=dict(prior['retained_parent_sources']);retained.update(prior['sources'])
assert retained==manifest['retained_parent_sources'] and len(retained)==37
def audit_retained():
 for name,row in retained.items():assert h(R/row['path'])==row['sha256'],('retained source drift',name)
audit_retained()

fixed={str(p):h(p) for p in (Path(__file__),M,PR,OBS,AUD,L)}
for n,v in manifest['sources'].items():
 assert h(D/'sources'/(n.replace('.','/')+'.lean'))==v['sha256']
 assert h(R/v['path'])==v['sha256'],('workspace drift before',n)
 assert not re.search(r'\b(?:sorry|admit)\b',(D/'sources'/(n.replace('.','/')+'.lean')).read_text()),('admission',n)
parent={};fallback={}
for n in manifest['order']:
 parent.update(scan(P/'lib'/n.replace('.','/')))
 for root in (PKG,TOOL):fallback.update(scan(root/n.replace('.','/')))
audit(parent);audit(fallback)
allruns=[]
try:
 for label in ('author','peer'):
  run=Path(tempfile.mkdtemp(prefix='ipra-quartic-model-'+label+'-'));lib=run/'lib';lib.mkdir(); subprocess.run(['cp','-as',str(P/'lib')+'/.',str(lib)+'/'],check=True)
  logs=D/label/'logs';logs.mkdir(parents=True,exist_ok=False);env=dict(os.environ,LEAN_PATH=str(lib)+':'+str(PKG),LEAN_NUM_THREADS='1');env.pop('LEAN_SRC_PATH',None)
  for n in manifest['order']:
   for suffix in S:
    p=Path(str(lib/n.replace('.','/'))+suffix)
    if os.path.lexists(p):assert p.is_symlink(),('refusing non-symlink output',str(p));p.unlink()
  guards={};rows=[]
  for n in manifest['order']:
   src=D/'sources'/(n.replace('.','/')+'.lean'); dep=subprocess.run([str(L),'--deps',str(src)],env=env,capture_output=True,text=True);assert dep.returncode==0 and not dep.stderr,(n,dep.stderr)
   inputs={}
   for line in dep.stdout.splitlines():
    p=Path(line);assert p.is_absolute() and p.is_file() and str(p).endswith('.olean') and any(p.is_relative_to(root) for root in (lib,PKG,TOOL)),(n,line)
    cur=scan(Path(str(p)[:-6]));
    for key,value in cur.items():assert key not in guards or guards[key]==value,('changed direct input',key);guards[key]=value
    key=str(p.relative_to(lib)) if p.is_relative_to(lib) else str(p);inputs[key]=h(p)
   audit(parent);audit(fallback);audit(guards)
   obj=lib/(n.replace('.','/')+'.olean');obj.parent.mkdir(parents=True,exist_ok=True);log=logs/(n.replace('.','_')+'.log')
   with log.open('x') as f:proc=subprocess.run([str(L),'-M8000','-j1','-DElab.async=false','--root='+str(D/'sources'),str(src),'-o',str(obj)],env=env,stdout=f,stderr=subprocess.STDOUT)
   text=log.read_text();assert proc.returncode==0 and obj.is_file() and 'error:' not in text and 'sorryAx' not in text and not re.search(r'\b(?:sorry|admit)\b',text),(n,proc.returncode,text)
   ws=warnings(text); reports=re.findall(r"^'[^']+' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)",text,re.M|re.S);expected={'DiophantineConsistency.IPRAQuartic86Native':1,'DiophantineConsistency.IPRAQuartic86NativeChecks':1}.get(n,0);assert len(reports)==expected,(n,reports)
   for report in reports:assert {x.strip() for x in report.split(',') if x.strip()} <= {'propext','Classical.choice','Quot.sound'},(n,report)
   rows.append({'module':n,'exit':proc.returncode,'source_sha256':h(src),'object_sha256':h(obj),'log_sha256':h(log),'direct_inputs':inputs,'warnings':ws});audit(parent);audit(fallback);audit(guards);print(label,n,'exit',proc.returncode,flush=True)
  assert fixed=={str(p):h(p) for p in (Path(__file__),M,PR,OBS,AUD,L)}
  for n,v in manifest['sources'].items():assert h(R/v['path'])==h(D/'sources'/(n.replace('.','/')+'.lean'))==v['sha256'],('source drift after',n)
  audit_retained();audit_previous()
  allruns.append({'label':label,'run':str(run),'rows':rows,'guards':guards})
 for a,b in zip(allruns[0]['rows'],allruns[1]['rows']):assert a==b,('row mismatch',a,b)
 out={'status':'MATCHED_PASS','fixed':fixed,'runs':allruns,'parent_output_guards':parent,'fallback_guards':fallback,'scope':manifest['boundary']};(D/'receipt.json').write_text(json.dumps(out,indent=2,sort_keys=True)+'\n');print('MATCHED_PASS',len(manifest['order']),'rows',flush=True)
except BaseException as e:
 (D/'failure.txt').write_text(repr(e)+'\n');raise
