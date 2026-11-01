#!/usr/bin/env python3
"""Focused paired replay; direct companions are pinned, inherited ancestry is explicit."""
from pathlib import Path
import hashlib,json,os,re,shutil,subprocess,tempfile
D=Path(__file__).resolve().parent; R=D.parents[3]; M=D/'manifest.json'
P=Path('/tmp/ipra-residual-squares-peer-i1lqlgip'); PR=R/'Computability/DiophantineConsistency/reviews/internal-residual-squares-model-replay/receipt.json'
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
assert h(M)=='0fec8d4d0674edbd3c9ccf16ab7697a2a54e933112e138f479905b6dd763a874'
manifest=json.loads(M.read_text()); assert manifest['status']=='FROZEN_FOCUSED_INPUT' and len(manifest['order'])==21 and len(set(manifest['order']))==21
receipt=json.loads(PR.read_text());assert receipt['status']=='MATCHED_PASS' and receipt['runs'][1]['run']==str(P)
for row in receipt['runs'][1]['rows']:assert h(P/'lib'/'DiophantineConsistency'/(row['module']+'.olean'))==row['object_sha256']
fixed={str(p):h(p) for p in (Path(__file__),M,PR,L)}
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
   ws=warnings(text); reports=re.findall(r'depends on axioms: \[([^\]]*)\]',text,re.S);expected={'DiophantineConsistency.SyntaxCoefficients':1,'DiophantineConsistency.IPRAQuarticExpressionBridge':1,'DiophantineConsistency.IPRAQuarticExpressionBridgeChecks':2,'DiophantineConsistency.QuarticCompiler':1,'DiophantineConsistency.QuarticSyntax':1,'DiophantineConsistency.IPRAQuarticModelBridge':1,'DiophantineConsistency.IPRAQuarticModelBridgeChecks':3}.get(n,0);assert len(reports)==expected,(n,reports)
   for report in reports:assert {x.strip() for x in report.split(',') if x.strip()} <= {'propext','Classical.choice','Quot.sound'},(n,report)
   rows.append({'module':n,'exit':proc.returncode,'source_sha256':h(src),'object_sha256':h(obj),'log_sha256':h(log),'direct_inputs':inputs,'warnings':ws});audit(parent);audit(fallback);audit(guards);print(label,n,'exit',proc.returncode,flush=True)
  assert fixed=={str(p):h(p) for p in (Path(__file__),M,PR,L)}
  for n,v in manifest['sources'].items():assert h(R/v['path'])==h(D/'sources'/(n.replace('.','/')+'.lean'))==v['sha256'],('source drift after',n)
  allruns.append({'label':label,'run':str(run),'rows':rows,'guards':guards})
 for a,b in zip(allruns[0]['rows'],allruns[1]['rows']):assert a==b,('row mismatch',a,b)
 out={'status':'MATCHED_PASS','fixed':fixed,'runs':allruns,'parent_output_guards':parent,'fallback_guards':fallback,'scope':manifest['boundary']};(D/'receipt.json').write_text(json.dumps(out,indent=2,sort_keys=True)+'\n');print('MATCHED_PASS',len(manifest['order']),'rows',flush=True)
except BaseException as e:
 (D/'failure.txt').write_text(repr(e)+'\n');raise
