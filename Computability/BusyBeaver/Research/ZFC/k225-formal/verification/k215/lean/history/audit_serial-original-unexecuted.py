#!/usr/bin/env python3
"""Compile explicit endpoint clients against the entirely fresh project closure."""
from pathlib import Path
import argparse,fcntl,hashlib,json,os,subprocess,time
P=Path(__file__).resolve().parent;W=P/'workspace';O=W/'.lake/build/lib/lean'
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
a=argparse.ArgumentParser();a.add_argument('source');a.add_argument('label');args=a.parse_args();src=Path(args.source).resolve();dest=P/'audit'/args.label;dest.mkdir(parents=True,exist_ok=False)
assert (P/'build-complete.json').is_file()
done=json.loads((P/'completed.json').read_text());assert len(done)==171
pins={}
for m,row in done.items():
 assert sha(row['source'])==row['source_sha256'],m
 obj=O/(m.replace('.','/')+'.olean');assert sha(obj)==row['object_sha256'],m
 pins[row['source']]=row['source_sha256'];pins.update(row['companions'])
for p,h in pins.items():assert sha(p)==h,p
pins[str(src)]=sha(src)
(dest/src.name).write_bytes(src.read_bytes())
cmd=['lake','env','lean','-j1','-M12288','--root='+str(src.parent),'-o',str(dest/(src.stem+'.olean')),str(src)]
row=dict(status='WAITING_SHARED_LOCK',command=cmd,cwd=str(W),source=str(src),source_sha256=sha(src),before=pins,timeout_seconds=120,memory_mebibytes=12288)
record=dest/'verification.json';record.write_text(json.dumps(row,indent=2)+'\n')
env=os.environ.copy();env.pop('LEAN_PATH',None);env['LEAN_NUM_THREADS']='1'
lock=open('/tmp/proveit-k215-proof-build.lock','a+');start=time.monotonic()
while True:
 try:fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB);break
 except BlockingIOError:time.sleep(.5)
row['lock_wait_seconds']=time.monotonic()-start;row['status']='COMPILING';record.write_text(json.dumps(row,indent=2)+'\n');start=time.monotonic()
try:
 with (dest/'compiler.log').open('wb')as f:
  try:rc=subprocess.run(cmd,cwd=W,env=env,stdout=f,stderr=subprocess.STDOUT,timeout=120).returncode;timeout=False
  except subprocess.TimeoutExpired:rc=-999;timeout=True
finally:fcntl.flock(lock,fcntl.LOCK_UN);lock.close()
row.update(status='PASS'if rc==0 else'FAIL',exit_code=rc,timed_out=timeout,seconds=time.monotonic()-start,log_sha256=sha(dest/'compiler.log'),after={p:sha(p)for p in pins})
row['inputs_unchanged']=row['before']==row['after'];assert row['inputs_unchanged']
row['fresh_companions']={str(p):sha(p)for p in dest.glob(src.stem+'.olean*')}
record.write_text(json.dumps(row,indent=2)+'\n');print(json.dumps({k:v for k,v in row.items()if k not in ('before','after')},indent=2));print((dest/'compiler.log').read_text());raise SystemExit(rc)
