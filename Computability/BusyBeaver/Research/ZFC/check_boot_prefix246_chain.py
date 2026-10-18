#!/usr/bin/env python3
"""Stage and serially check exact246 bootstrap units against explicit checked parents.

--prepare-only makes no Lean or version calls. Full mode checks one source/audit
pair at a time; each original guard retains its shared120-second limit. No
source, generator or dependency build is run by this coordinator.
"""
from pathlib import Path
import argparse,ast,hashlib,json,subprocess,sys
HERE=Path(__file__).resolve().parent
REPO=HERE.parents[3]
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def need(c,m):
 if not c:raise RuntimeError(m)
def dump(p,x):p.parent.mkdir(parents=True,exist_ok=True);p.write_text(json.dumps(x,indent=2)+'\n')
def main():
 ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--repo',type=Path,default=REPO);ap.add_argument('--output',type=Path,required=True);ap.add_argument('--prepare-only',action='store_true');a=ap.parse_args();repo=a.repo.resolve();out=a.output.resolve();need(not out.is_relative_to(repo) and not out.exists(),'Use a new external output directory.')
 research=repo/'Computability/BusyBeaver/Research/ZFC';mf=research/'bootstrap-prefix246/manifest.json';manifest=json.loads(mf.read_text());need(manifest['status']=='EXACT_COMPLETED_BOOTSTRAP_EVIDENCE_PACKET' and manifest['blank_endpoint']==410735,'Incomplete publication manifest.')
 def published(binding):
  p=repo/binding['path'];need(sha(p)==binding['sha256'],'Published input changed: '+str(p));return p
 for h,row in manifest['content_registry'].items():need(sha(repo/row['published_path'])==h,'Content registry mismatch.')
 first=published(manifest['first_checkpoint']);firstrec=json.loads(first.read_text());need(firstrec['status']=='PASS','First1024 boundary is not PASS.')
 units=manifest['units'];need([u['name'] for u in units]==['probe16384']+[f'group{i:02}' for i in range(1,9)],'Unexpected serial order.')
 rawgen=published(manifest['shared_programs']['generate.py']);rawtemplate=published(manifest['shared_programs']['check-template.py']);probegen=published(manifest['shared_programs']['probe_generator'])
 out.mkdir();record={'status':'PREPARING' if a.prepare_only else 'RUNNING','manifest_sha256':sha(mf),'coordinator_sha256':sha(Path(__file__).resolve()),'prepare_only':a.prepare_only,'units':[],'commands':[],'dependency_build':False,'compiler_version_query_performed':False};dump(out/'coordination.json',record)
 produced={}
 for unit in units:
  name=unit['name'];stage=out/'units'/name;stage.mkdir(parents=True);art=unit['artifacts'];src=published(art['source']);aud=published(art['audit']);data=published(art['data']);rawguard=published(art['executed_guard']);historical=published(art['verification'])
  (stage/src.name).write_bytes(src.read_bytes());(stage/'Audit.lean').write_bytes(aud.read_bytes());(stage/'data.json').write_bytes(data.read_bytes())
  text=rawguard.read_text()
  if name=='probe16384':
   # Only repository/parent defaults are adapted. All proof/audit/limit logic is exact.
   text=text.replace("REPO=Path('/home/codex/.codex/worktrees/ec20/Proofs')",'REPO=Path('+repr(str(repo))+')')
   text=text.replace("P=HERE.parent/'fast/run1/verification.json'","P=REPO/'Computability/BusyBeaver/Research/ZFC/results/fast-table-prefix246-verification.json'")
   (stage/'generate.py').write_bytes(probegen.read_bytes())
  else:
   cfg=next(ast.literal_eval(n.value) for n in ast.parse(text).body if isinstance(n,ast.Assign) and any(isinstance(t,ast.Name) and t.id=='CFG' for t in n.targets))
   parents=[]
   index=int(name[5:]);parentname='first' if index==1 else f'group{index-1:02}'
   for old in cfg['parents']:
    if old['module'].endswith('BootPrefix246Probe16384'):pn='probe16384'
    else:pn=parentname
    if pn=='first':pp=first
    elif a.prepare_only:pp=published(next(u for u in units if u['name']==pn)['artifacts']['verification'])
    else:pp=produced[pn]
    parents.append(dict(path=str(pp),sha256=sha(pp),module=old['module']))
   cfg.update(parents=parents,generator=str(rawgen),generator_sha256=sha(rawgen),template=str(rawtemplate),template_sha256=sha(rawtemplate))
   text=rawtemplate.read_text().replace('__CONFIG__',repr(cfg)).replace("REPO=Path('/home/codex/.codex/worktrees/ec20/Proofs')",'REPO=Path('+repr(str(repo))+')')
  guard=stage/'check.py';guard.write_text(text);result=stage/'result';cmd=[sys.executable,'-B',str(guard),'--output',str(result)]+(['--prepare-only'] if a.prepare_only else [])
  note=dict(name=name,historical_record_sha256=sha(historical),staged_source_sha256=sha(stage/src.name),staged_audit_sha256=sha(stage/'Audit.lean'),adapted_guard_sha256=sha(guard),source_audit_data_identical=True);record['units'].append(note);dump(out/'coordination.json',record)
  completed=subprocess.run(cmd,cwd=out,capture_output=True,text=True);log=stage/'coordinator-output.log';log.write_text(completed.stdout+completed.stderr);record['commands'].append(dict(unit=name,command=cmd,exit_code=completed.returncode,log=str(log)));dump(out/'coordination.json',record)
  need(completed.returncode==0,'Unit guard failed: '+name)
  vr=result/'verification.json';r=json.loads(vr.read_text());expected='PREPARED_NOT_BUILT' if a.prepare_only else 'PASS';need(r['status']==expected,'Unexpected unit result.')
  if a.prepare_only:need(r['commands']==[] and r['fresh_modules']==[] and r['compiler_version_query_performed'] is False,'Preparation invoked proof commands.')
  else:need(r['only_standard_axioms'] and r['all_input_provider_postchecks'] and r['all_fresh_objects_unchanged_after_audit'],'Incomplete replay result.')
  note.update(status=r['status'],record=str(vr),record_sha256=sha(vr));produced[name]=vr;dump(out/'coordination.json',record)
 record['status']='PREPARED_NOT_BUILT' if a.prepare_only else 'PASS';dump(out/'coordination.json',record);print(out/'coordination.json')
if __name__=='__main__':main()
