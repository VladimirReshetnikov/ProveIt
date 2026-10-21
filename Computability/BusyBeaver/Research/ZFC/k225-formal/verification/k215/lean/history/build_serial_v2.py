#!/usr/bin/env python3
"""Serial fresh current-source KEndpoint215 closure; shared compiler lock."""
from pathlib import Path
import fcntl,hashlib,json,os,signal,subprocess,sys,time
P=Path(__file__).resolve().parent;ROOT=Path('/home/codex/.codex/worktrees/ec20/Proofs');W=P/'workspace';OUT=W/'.lake/build/lib/lean';OUT.mkdir(parents=True,exist_ok=True)
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def write(p,x):p.write_text(json.dumps(x,indent=2)+'\n')
I=json.loads((P/'inventory-v2.json').read_text());donefile=P/'completed.json';done=json.loads(donefile.read_text())if donefile.exists()else{};attemptfile=P/'attempts.json';attempts=json.loads(attemptfile.read_text())if attemptfile.exists()else[]
env=os.environ.copy();env['LEAN_NUM_THREADS']='1';env.pop('LEAN_PATH',None)
for entry in I['project_modules']:
 m=entry['module'];src=ROOT/entry['relative_source'];h=sha(src);obj=OUT/(m.replace('.','/')+'.olean');deps={d:done[d]['object_sha256']for d in entry['imports']if d in done};prev=done.get(m)
 if prev and prev['source_sha256']==h and prev['dependencies']==deps and obj.is_file()and prev['object_sha256']==sha(obj):continue
 index=len(attempts)+1;log=P/'logs'/f'{index:04d}-{m}.log';prefix=m.replace('.','/')+'.lean';source_root=str(src)[:-len(prefix)].rstrip('/');obj.parent.mkdir(parents=True,exist_ok=True)
 cmd=['lake','env','lean','-j1','-M12288','--root='+source_root,'-o',str(obj),str(src)]
 row=dict(index=index,module=m,source=str(src),source_sha256=h,dependencies=deps,command=cmd,cwd=str(W),log=str(log),status='WAITING_SHARED_LOCK',memory_mebibytes=12288,timeout_seconds=900)
 attempts.append(row);write(attemptfile,attempts);print('WAIT',index,m,flush=True)
 lock=open('/tmp/proveit-k215-proof-build.lock','a+');waitstart=time.monotonic()
 while True:
  try:fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB);break
  except BlockingIOError:time.sleep(.5)
 row['lock_wait_seconds']=time.monotonic()-waitstart;row['status']='COMPILING';write(attemptfile,attempts);print('BUILD',index,m,flush=True);begun=time.monotonic()
 try:
  with log.open('wb')as stream:
   proc=subprocess.Popen(cmd,cwd=W,env=env,stdout=stream,stderr=subprocess.STDOUT,start_new_session=True)
   try:rc=proc.wait(timeout=900);timed=False
   except subprocess.TimeoutExpired:
    os.killpg(proc.pid,signal.SIGKILL);proc.wait();rc=-999;timed=True
 finally:fcntl.flock(lock,fcntl.LOCK_UN);lock.close()
 row.update(status='PASS'if rc==0 else'FAIL',exit_code=rc,timed_out=timed,seconds=time.monotonic()-begun,log_sha256=sha(log),source_unchanged=sha(src)==h)
 assert row['source_unchanged'];write(attemptfile,attempts)
 print(row['status'],m,round(row['seconds'],3),flush=True)
 if rc:print(log.read_text()[-12000:],flush=True);sys.exit(1)
 assert obj.is_file();row['object_sha256']=sha(obj);row['companions']={str(x):sha(x)for x in sorted(obj.parent.glob(obj.stem+'.olean*'))};done[m]=row;write(donefile,done);write(attemptfile,attempts)
write(P/'build-complete.json',dict(status='FULL_CURRENT_SOURCE_CLOSURE_PASS',target=I['target'],modules=len(done),compiler_lock='/tmp/proveit-k215-proof-build.lock',external_imports=I['direct_external_imports'],completed_sha256=sha(donefile)))
print('COMPLETE',len(done),flush=True)
