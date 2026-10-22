#!/usr/bin/env python3
"""Fresh serial proof builds of either alternative, with source/import SHA-256 evidence."""
import argparse, datetime, fcntl, hashlib, json, os, re, subprocess, time
from pathlib import Path
p=argparse.ArgumentParser()
p.add_argument('--repo',type=Path,required=True)
p.add_argument('--lean',type=Path,required=True)
p.add_argument('--variant',choices=['local','shared'],required=True)
a=p.parse_args();repo=a.repo.resolve();lean=a.lean.resolve();here=Path(__file__).resolve().parent
variant=here/('local-only' if a.variant=='local' else 'overlay')
roots=[variant,here/'audit'/a.variant,repo/'Computability/BusyBeaver/Lean',repo/'Logic/FirstOrder/Lean',repo/'SetTheory/ZF/Lean']
lib=here/'build-final'/a.variant;ev=here/'evidence'/a.variant
lib.mkdir(parents=True,exist_ok=True);ev.mkdir(parents=True,exist_ok=True)
env=os.environ.copy();env['LEAN_PATH']=str(lib)
seen=set();order=[];imports={};hashes={}
def sha(data):return hashlib.sha256(data).hexdigest()
def find(mod):
 for root in roots:
  f=root/(mod.replace('.','/')+'.lean')
  if f.exists():return f
 return None
def visit(mod):
 if mod in seen:return
 seen.add(mod);f=find(mod)
 if not f:
  if not mod.startswith(('Init','Lean','Std')):raise RuntimeError('Missing source '+mod)
  return
 deps=[]
 for line in f.read_text().splitlines():
  if line.startswith('import '):deps.extend(line[7:].split())
 for m in deps:visit(m)
 imports[mod]=deps;order.append((mod,f))
visit('AXAudit')
manifest={'variant':a.variant,'started_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
 'repository_commit':subprocess.check_output(['git','-C',str(repo),'rev-parse','HEAD'],text=True).strip(),
 'lean_version':subprocess.check_output([str(lean),'--version'],text=True).strip(),
 'targets':['AXAudit'],'modules':[],'fresh_build':True,'success':False}
for mod,f in order:
 out=lib/(mod.replace('.','/')+'.olean');out.parent.mkdir(parents=True,exist_ok=True)
 source_hash=sha(f.read_bytes())
 bound={'source_sha256':source_hash,'imports':{m:hashes.get(m,'compiler-standard-library') for m in imports[mod]}}
 hashes[mod]=sha(json.dumps(bound,sort_keys=True).encode())
 print('BUILD',mod,flush=True);t=time.monotonic()
 with open('/tmp/proveit-k215-proof-build.lock','w') as lock, (ev/(mod+'.log')).open('w') as log:
  fcntl.flock(lock,fcntl.LOCK_EX)
  result=subprocess.run([str(lean),'-o',str(out),str(f)],stdout=log,stderr=subprocess.STDOUT,env=env)
 record={'module':mod,'source':str(f),'source_sha256':source_hash,'imports':bound['imports'],
  'transitive_source_sha256':hashes[mod],'exit_code':result.returncode,'seconds':round(time.monotonic()-t,3)}
 if result.returncode==0:record['olean_sha256']=sha(out.read_bytes())
 manifest['modules'].append(record)
 (ev/'build.json').write_text(json.dumps(manifest,indent=2)+'\n')
 if result.returncode:
  print((ev/(mod+'.log')).read_text(),flush=True);raise SystemExit(result.returncode)
manifest['success']=True
manifest['finished_utc']=datetime.datetime.now(datetime.timezone.utc).isoformat()
(ev/'build.json').write_text(json.dumps(manifest,indent=2)+'\n')
print('SUCCESS',len(order),'modules freshly compiled',flush=True)
