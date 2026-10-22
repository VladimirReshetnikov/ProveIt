#!/usr/bin/env python3
"""Compile the complete isolated shared-basis component and retain source-bound evidence."""
from pathlib import Path
import argparse,fcntl,hashlib,json,os,subprocess,time

p=argparse.ArgumentParser();p.add_argument('--lean',required=True);args=p.parse_args()
here=Path(__file__).resolve().parent;src=here/'src';out=here/'build';out.mkdir(exist_ok=True)
logs=out/'logs';logs.mkdir(exist_ok=True)
info=json.loads((here/'sources.json').read_text())
receipt={'baseline':info['baseline'],'proposal':info['proposal'],'scope':'fresh component build; full endpoint not rebuilt',
    'compiler':subprocess.check_output([args.lean,'--version'],text=True).strip(),'modules':[]}
for name in info['order']:
    rel=Path(*name.split('.'));s=(src/rel).with_suffix('.lean');o=(out/rel).with_suffix('.olean');o.parent.mkdir(parents=True,exist_ok=True)
    with open('/tmp/proveit-k215-proof-build.lock','a+b') as lock:
        fcntl.flock(lock,fcntl.LOCK_EX)
        t=time.monotonic();r=subprocess.run([args.lean,'-o',str(o),str(s.relative_to(src))],cwd=src,env=dict(os.environ,LEAN_PATH=str(out)),capture_output=True,text=True);elapsed=time.monotonic()-t
        fcntl.flock(lock,fcntl.LOCK_UN)
    log=logs/(name+'.log');log.write_text(r.stdout+r.stderr)
    entry={'module':name,'source_sha256':hashlib.sha256(s.read_bytes()).hexdigest(),'exit':r.returncode,'seconds':elapsed,
      'log_sha256':hashlib.sha256(log.read_bytes()).hexdigest(),'object_sha256':hashlib.sha256(o.read_bytes()).hexdigest() if o.exists() else None}
    receipt['modules'].append(entry);(out/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print(name,r.returncode,round(elapsed,3),flush=True)
    if r.returncode:print(r.stdout+r.stderr);raise SystemExit(r.returncode)
receipt['all_passed']=True;(out/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
