#!/usr/bin/env python3
"""Compile the complete CM215 endpoint over a freshly checked K215 closure."""
from pathlib import Path
import argparse,fcntl,hashlib,json,os,re,subprocess,time,sys,shutil
from source_scope import check_source_scope
W=Path(__file__).resolve().parent
p=argparse.ArgumentParser(description=__doc__)
p.add_argument('--base-build',type=Path,required=True)
p.add_argument('--source',type=Path,required=True)
p.add_argument('--out',type=Path,required=True)
p.add_argument('--lean',required=True)
a=p.parse_args()
B=a.base_build.resolve();S=a.source.resolve();O=a.out.resolve()
LEAN=Path(shutil.which(a.lean) or a.lean).resolve()
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
base=json.loads((B/'verification.json').read_text())
assert base['status']=='PASS'
assert sha(B/'completed.json')==base['completed_sha256']
assert sha(B/'inventory.json')==base['inventory_sha256']
source_scope=check_source_scope(B,W)
completed=json.loads((B/'completed.json').read_text())
for r in completed.values():
 assert sha(r['source'])==r['source_sha256']
 assert all(sha(p)==h for p,h in r['companions'].items())
 assert sha(r['log'])==r['log_sha256']
assert sha(LEAN)==base['toolchain']['lean_sha256']
for row in json.loads((S/'sources.json').read_text()):
 assert sha(S/row['file'])==row['sha256'],row['file']
assert not O.exists(),'Use a fresh output directory; existing objects could shadow checked dependencies'
O.mkdir(parents=True)
modules=['PositiveStutter','CM215Tables','CM215Invariant','CM215Transfer','CM215CoreBridge','CM215Dense','CM215Endpoint','CM215Audit']
assert not (O/'integration_receipt.json').exists(),'Use fresh output'
env=os.environ.copy();env['LEAN_PATH']=str(O)+':'+str(B/'workspace/.lake/build/lib/lean');env['LEAN_NUM_THREADS']='1'
receipt={'status':'RUNNING','base_pin':'56e487ce8fa4cf63ad169ffe0cd2944e9fc62dd3','baseline_source_scope':source_scope,'base_closure_modules':base['project_modules'],'base_verification_sha256':sha(B/'verification.json'),'base_completed_sha256':sha(B/'completed.json'),'lean_sha256':sha(LEAN),'modules':[],'axiom_reports':{}}
receipt.update(driver_sha256=sha(__file__),source_scope_sha256=sha(W/'source_scope.py'))
def save(): (O/'integration_receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
save()
with open('/tmp/proveit-k215-proof-build.lock','a+') as lock:
 fcntl.flock(lock,fcntl.LOCK_EX)
 for name in modules:
  src=S/(name+'.lean');obj=O/(name+'.olean');log=O/(name+'.log');before=sha(src)
  command=[str(LEAN),'-j1','-M4096','--root='+str(S),'-o',str(obj),str(src)]
  print('CHECK',name,flush=True);t=time.monotonic()
  with log.open('wb') as f:
   try:r=subprocess.run(command,cwd=S,env=env,stdout=f,stderr=subprocess.STDOUT,timeout=900)
   except subprocess.TimeoutExpired:
    receipt['status']='TIMEOUT';save();raise
  row={'module':name,'source_sha256':before,'source_unchanged':sha(src)==before,'command':command,'returncode':r.returncode,'seconds':time.monotonic()-t,'log_sha256':sha(log)}
  assert row['source_unchanged'],('Source changed during compilation',name)
  receipt['modules'].append(row);save()
  if r.returncode:receipt['status']='FAIL';save();sys.exit('FAILED '+name+': '+str(log))
  row['object_sha256']=sha(obj)
  row['companions']={str(p):sha(p) for p in sorted(obj.parent.glob(obj.stem+'.olean*'))}
  text=log.read_text();reports={k:[a.strip() for a in v.split(',') if a.strip()] for k,v in re.findall(r"'([^']+)' depends on axioms: \[([^]]*)\]",text,re.S)}
  for k in re.findall(r"'([^']+)' does not depend on any axioms",text):reports[k]=[]
  for k,axioms in reports.items():assert set(axioms)<={'propext','Quot.sound','Classical.choice'},(k,axioms)
  assert 'sorryAx' not in text and 'ofReduceBool' not in text
  receipt['axiom_reports'].update(reports);save();print('PASS',name,round(row['seconds'],3),flush=True)
 required=['SetTheory.BusyBeaver.ZFC.CM215Endpoint.blank_halts_iff_zfc_refutation','SetTheory.BusyBeaver.ZFC.CM215Endpoint.nonhalting_iff_zfc_consistency','CM215.IntegrationAudit.exact_finite_run_endpoint','CM215.IntegrationAudit.exact_nonhalting_endpoint','CM215.IntegrationAudit.literal_rows']
 assert all(k in receipt['axiom_reports'] for k in required)
receipt['status']='PASS';save();print('COMPLETE',len(modules),'integration modules',flush=True)
