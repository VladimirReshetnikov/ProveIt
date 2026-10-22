#!/usr/bin/env python3
"""Check the three-induction refactor and every affected endpoint dependency."""
from pathlib import Path
import argparse,fcntl,hashlib,json,os,re,shutil,subprocess,time,sys
from source_scope import check_source_scope, check_calculus_overlay
HERE=Path(__file__).resolve().parent
p=argparse.ArgumentParser(description=__doc__)
p.add_argument('--base-build',type=Path,required=True)
p.add_argument('--cm-build',type=Path,required=True)
p.add_argument('--source-repo',type=Path,required=True)
p.add_argument('--out',type=Path,required=True)
p.add_argument('--lean',required=True)
a=p.parse_args();B=a.base_build.resolve();C=a.cm_build.resolve();R=a.source_repo.resolve();O=a.out.resolve();LEAN=Path(shutil.which(a.lean) or a.lean).resolve()
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
base=json.loads((B/'verification.json').read_text());cm=json.loads((C/'integration_receipt.json').read_text());assert base['status']==cm['status']=='PASS'
assert sha(B/'completed.json')==base['completed_sha256']
assert sha(B/'inventory.json')==base['inventory_sha256']
assert sha(B/'verification.json')==cm['base_verification_sha256']
source_scope=check_source_scope(B,HERE)
assert source_scope==cm['baseline_source_scope']
completed=json.loads((B/'completed.json').read_text())
for row in completed.values():
 assert sha(row['source'])==row['source_sha256']
 assert all(sha(p)==h for p,h in row['companions'].items())
 assert sha(row['log'])==row['log_sha256']
for row in cm['modules']:
 assert sha(HERE/'cm215'/(row['module']+'.lean'))==row['source_sha256']
 assert sha(C/(row['module']+'.log'))==row['log_sha256']
 assert sha(C/(row['module']+'.olean'))==row['object_sha256']
 assert all(sha(p)==h for p,h in row['companions'].items())
assert sha(LEAN)==base['toolchain']['lean_sha256']
overlay_binding=check_calculus_overlay(HERE,R)
assert not O.exists(),'Use a new output directory';O.mkdir(parents=True)
rows=json.loads((HERE/'calculus/affected.json').read_text())
inventory=json.loads((B/'inventory.json').read_text())['modules']
affected={'BusyBeaver.ZFC.KSeedModel222'}
for row in inventory:
 if any(dep in affected for dep in row['imports']):affected.add(row['module'])
assert [row['module'] for row in rows]==[row['module'] for row in inventory if row['module'] in affected]
for row in rows:
 assert sha(R/row['path'])==row['sha256'],row['path']
# Lean selects the first matching package root. Populate that root with only
# verified, unaffected imports; changed modules must be compiled into new files.
cache=B/'workspace/.lake/build/lib/lean'
reused={}
for entry in inventory:
 name=entry['module']
 if name in affected:continue
 links={}
 for path,h in completed[name]['companions'].items():
  src=Path(path);dst=O/src.relative_to(cache)
  assert sha(src)==h
  dst.parent.mkdir(parents=True,exist_ok=True);assert not dst.exists()
  dst.symlink_to(src)
  links[str(dst)]={'source':str(src),'sha256':h}
 reused[name]=links
assert len(reused)==174
env=os.environ.copy();env['LEAN_PATH']=os.pathsep.join([str(O),str(C),str(B/'workspace/.lake/build/lib/lean')]);env['LEAN_NUM_THREADS']='1'
receipt={'status':'RUNNING','base_pin':'56e487ce8fa4cf63ad169ffe0cd2944e9fc62dd3','baseline_source_scope':source_scope,'base_verification_sha256':sha(B/'verification.json'),'cm_integration_sha256':sha(C/'integration_receipt.json'),'changed_module':'BusyBeaver.ZFC.KSeedModel222','overlay_binding':overlay_binding,'patch_sha256':sha(HERE/'calculus/REMOVE_THREE_INDUCTIONS.patch'),'affected_modules':[x['module'] for x in rows],'unchanged_project_modules':len(inventory)-len(rows),'modules':[],'axiom_reports':{}}
receipt.update(driver_sha256=sha(__file__),source_scope_sha256=sha(HERE/'source_scope.py'),final_byte_identical_project_modules=179,final_proof_only_modified_project_modules=5)
receipt['unaffected_project_import_links']=reused
def save():(O/'calculus_receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
save()
specs=[]
for row in rows:
 m=row['module'];rel=m.replace('.','/')+'.lean'
 if m=='BusyBeaver.ZFC.KSeedModel222':src=HERE/'calculus'/rel;root=HERE/'calculus'
 else:src=R/row['path'];root=Path(str(src)[:-len(rel)])
 specs.append((m,src,root))
for m in ['EndpointAudit215','K215Audit']:
 root=R/'Computability/BusyBeaver/Research/ZFC/k225-formal/verification/k215/lean';specs.append((m,root/(m+'.lean'),root))
for m in ['CM215Endpoint','CM215Audit']:specs.append((m,HERE/'cm215'/(m+'.lean'),HERE/'cm215'))
for m,src,root in specs:
 obj=O/(m.replace('.','/')+'.olean');obj.parent.mkdir(parents=True,exist_ok=True);log=O/(m+'.log');before=sha(src);command=[str(LEAN),'-j1','-M12288','--root='+str(root),'-o',str(obj),str(src)]
 with open('/tmp/proveit-k215-proof-build.lock','a+') as lock:
  fcntl.flock(lock,fcntl.LOCK_EX);print('CHECK',m,flush=True);t=time.monotonic()
  with log.open('wb') as f:r=subprocess.run(command,cwd=root,env=env,stdout=f,stderr=subprocess.STDOUT,timeout=900)
 row={'module':m,'source_sha256':before,'source_unchanged':sha(src)==before,'command':command,'returncode':r.returncode,'seconds':time.monotonic()-t,'log_sha256':sha(log)};receipt['modules'].append(row);save()
 assert row['source_unchanged'],('Source changed during compilation',m)
 if r.returncode:receipt['status']='FAIL';save();sys.exit('FAILED '+m+': '+str(log))
 row['object_sha256']=sha(obj);row['companions']={str(p):sha(p) for p in sorted(obj.parent.glob(obj.stem+'.olean*'))};text=log.read_text()
 reports={k:[a.strip() for a in v.split(',') if a.strip()] for k,v in re.findall(r"'([^']+)' depends on axioms: \[([^]]*)\]",text,re.S)}
 for k in re.findall(r"'([^']+)' does not depend on any axioms",text):reports[k]=[]
 for k,ax in reports.items():assert set(ax)<={'propext','Quot.sound','Classical.choice'},(k,ax)
 assert 'sorryAx' not in text and 'ofReduceBool' not in text
 receipt['axiom_reports'].update(reports);save();print('PASS',m,round(row['seconds'],3),flush=True)
for k in ['SetTheory.BusyBeaver.ZFC.KSeed222.seed_eqFree','SetTheory.BusyBeaver.ZFC.KEndpoint215.blank_halts_iff_zfc_refutation','SetTheory.BusyBeaver.ZFC.CM215Endpoint.blank_halts_iff_zfc_refutation','CM215.IntegrationAudit.exact_finite_run_endpoint','CM215.IntegrationAudit.exact_nonhalting_endpoint']:
 assert k in receipt['axiom_reports'],k
for links in reused.values():
 for dst,row in links.items():
  assert Path(dst).is_symlink() and Path(dst).resolve()==Path(row['source']).resolve()
  assert sha(dst)==row['sha256']==sha(row['source'])
receipt['status']='PASS';save();print('COMPLETE',len(rows),'affected project modules and 4 endpoint/audit clients')
