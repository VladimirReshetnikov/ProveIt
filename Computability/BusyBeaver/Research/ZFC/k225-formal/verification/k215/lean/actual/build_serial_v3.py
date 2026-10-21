#!/usr/bin/env python3
"""Resume fresh current-source closure with the reviewed group-safe serial supervisor."""
from pathlib import Path
import hashlib,importlib.util,json,os,signal,sys
P=Path(__file__).resolve().parent;ROOT=Path('/home/codex/.codex/worktrees/ec20/Proofs');W=P/'workspace';OUT=W/'.lake/build/lib/lean'
SUP=P/'portable-supervisor.py';spec=importlib.util.spec_from_file_location('supervisor',SUP);sup=importlib.util.module_from_spec(spec);spec.loader.exec_module(sup)
sha=sup.sha
I=json.loads((P/'inventory-v3.json').read_text());entries={r['module']:r for r in I['project_modules']}
donefile=P/'completed.json';done=json.loads(donefile.read_text());attemptfile=P/'attempts.json';attempts=json.loads(attemptfile.read_text())
assert set(done)<=set(entries)
env=os.environ.copy();env['LEAN_NUM_THREADS']='1';env.pop('LEAN_PATH',None)
def interrupt(signum,frame):raise KeyboardInterrupt(f'Signal {signum}')
signal.signal(signal.SIGTERM,interrupt)
for entry in I['project_modules']:
 m=entry['module'];src=ROOT/entry['relative_source'];h=sha(src);assert h==entry['sha256'],m
 obj=OUT/(m.replace('.','/')+'.olean');expected=set(entry['imports'])&set(entries);assert expected<=done.keys(),m
 deps={d:done[d]['object_sha256'] for d in expected};prev=done.get(m)
 if (prev and prev['source_sha256']==h and prev['dependencies']==deps and obj.is_file() and prev['object_sha256']==sha(obj)
     and prev['companions'] and all(Path(p).is_file() and sha(p)==x for p,x in prev['companions'].items())
     and Path(prev['log']).is_file() and sha(prev['log'])==prev['log_sha256']):continue
 index=len(attempts)+1;log=P/'logs'/f'{index:04d}-{m}.log';prefix=m.replace('.','/')+'.lean';source_root=str(src)[:-len(prefix)].rstrip('/');obj.parent.mkdir(parents=True,exist_ok=True)
 cmd=['lake','env','lean','-j1','-M12288','--root='+source_root,'-o',str(obj),str(src)]
 row=dict(index=index,module=m,source=str(src),source_sha256=h,dependencies=deps,command=cmd,cwd=str(W),log=str(log),status='WAITING_SHARED_LOCK',memory_mebibytes=12288,timeout_seconds=900,supervisor_sha256=sha(SUP),inventory_sha256=sha(P/'inventory-v3.json'))
 attempts.append(row);sup.save(attemptfile,attempts);print('CHECK',index,m,flush=True)
 try:ok=sup.run_locked(cmd,W,env,Path('/tmp/proveit-k215-proof-build.lock'),log,900,row,P/'current-command.json')
 except BaseException:
  sup.save(attemptfile,attempts);raise
 row['source_unchanged']=sha(src)==h;assert row['source_unchanged'];sup.save(attemptfile,attempts)
 print(row['status'],m,round(row['seconds'],3),flush=True)
 if not ok:print(log.read_text()[-18000:],flush=True);sys.exit(1)
 assert obj.is_file();row['object_sha256']=sha(obj);row['companions']={str(x):sha(x) for x in sorted(obj.parent.glob(obj.stem+'.olean*'))};done[m]=row;sup.save(donefile,done);sup.save(attemptfile,attempts)
assert set(done)==set(entries)
for m,e in entries.items():assert done[m]['dependencies']=={d:done[d]['object_sha256'] for d in e['imports'] if d in entries},m
sup.save(P/'build-complete.json',dict(status='FULL_CURRENT_SOURCE_CLOSURE_PASS',target=I['target'],modules=len(done),compiler_lock='/tmp/proveit-k215-proof-build.lock',external_imports=I['direct_external_imports'],completed_sha256=sha(donefile),inventory_sha256=sha(P/'inventory-v3.json'),exact_module_set=True,exact_dependencies=True))
print('COMPLETE',len(done),flush=True)
