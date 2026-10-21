#!/usr/bin/env python3
"""Rebuild the 26-source dependency closure and the typed public-API client."""
from pathlib import Path
import argparse,hashlib,json,os,re,shutil,subprocess,sys,time
p=argparse.ArgumentParser()
p.add_argument('--lean',default=shutil.which('lean') or 'lean')
p.add_argument('--output',type=Path)
p.add_argument('--lock',type=Path)
a=p.parse_args();root=Path(__file__).resolve().parent;src=root/'lean';out=(a.output or root/'replay-output').resolve()
manifest=json.loads((root/'source-manifest.json').read_text())
for f in manifest['files']:
 actual=hashlib.sha256((root/f['path']).read_bytes()).hexdigest()
 if actual!=f['sha256']:raise SystemExit('Source hash mismatch: '+f['path'])
version=subprocess.check_output([a.lean,'--version'],text=True).strip()
if 'version 4.32.0,' not in version:raise SystemExit('Expected Lean 4.32.0, got '+version)
seen=set();order=[]
def visit(m):
 if m in seen:return
 seen.add(m);f=src/(m.replace('.','/')+'.lean')
 if not f.is_file():raise SystemExit('Missing module '+m)
 for line in f.read_text().splitlines():
  if line.startswith('import '):
   for d in line[7:].split():visit(d)
 order.append(m)
visit('AuditSeedSemantics')
(out/'logs').mkdir(parents=True,exist_ok=True)
records=[]
for m in order:
 f=src/(m.replace('.','/')+'.lean');obj=out/(m.replace('.','/')+'.olean');obj.parent.mkdir(parents=True,exist_ok=True)
 cmd=[a.lean,'-o',str(obj),str(f)];log=out/'logs'/(m+'.log')
 lock=None
 if a.lock:
  import fcntl
  lock=a.lock.open('w');fcntl.flock(lock,fcntl.LOCK_EX)
 st=time.monotonic()
 try:
  with log.open('w') as stream:
   proc=subprocess.run(cmd,cwd=src,env={**os.environ,'LEAN_PATH':str(out)},stdout=stream,stderr=subprocess.STDOUT)
 finally:
  if lock:lock.close()
 record={'module':m,'command':cmd,'status':proc.returncode,'seconds':time.monotonic()-st,'source_sha256':hashlib.sha256(f.read_bytes()).hexdigest(),'object_sha256':hashlib.sha256(obj.read_bytes()).hexdigest() if obj.exists() else None,'log_sha256':hashlib.sha256(log.read_bytes()).hexdigest()}
 records.append(record)
 result={'status':'PASS' if len(records)==len(order) and all(x['status']==0 for x in records) else 'INCOMPLETE','toolchain':version,'upstream_commit':manifest['upstream_commit'],'records':records}
 (out/'verification.json').write_text(json.dumps(result,indent=2)+'\n')
 print(m,proc.returncode,flush=True)
 if proc.returncode or 'sorryAx' in log.read_text():
  print(log.read_text());raise SystemExit(proc.returncode or 2)
print('PASS:',len(records),'modules, including the exact public-API client.')
print((out/'logs/AuditSeedSemantics.log').read_text())
