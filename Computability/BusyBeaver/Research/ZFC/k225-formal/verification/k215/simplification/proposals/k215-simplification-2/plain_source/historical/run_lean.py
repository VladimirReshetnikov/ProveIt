#!/usr/bin/env python3
"""Serial one-file Lean runner with exact source/output hashes and invocation logs."""
import argparse,hashlib,json,os,resource,subprocess,time
from pathlib import Path
p=argparse.ArgumentParser();p.add_argument('source',type=Path);p.add_argument('--lean',type=Path,default=Path('/dev/shm/zfc_59b6900405ab/lean-4.32.0-linux/bin/lean'));p.add_argument('--root',type=Path);p.add_argument('--timeout',type=int,default=300);p.add_argument('--logs',type=Path);args=p.parse_args()
source=args.source.resolve();root=(args.root or source.parent).resolve();logs=(args.logs or source.parent/'build_logs').resolve();logs.mkdir(parents=True,exist_ok=True)
obj=source.with_suffix('.olean');cmd=[str(args.lean),'-o',str(obj),str(source)];env=dict(os.environ);env['LEAN_PATH']=str(root)
key=source.stem;start=time.time()
try:
 run=subprocess.run(cmd,cwd=root,env=env,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,timeout=args.timeout);out=run.stdout;rc=run.returncode
except subprocess.TimeoutExpired as e:
 out=e.stdout or b'';rc=124
elapsed=time.time()-start
(logs/(key+'.log')).write_bytes(out)
sha=lambda x:hashlib.sha256(x).hexdigest()
record={'source':str(source.relative_to(root)),'source_sha256':sha(source.read_bytes()),'command':cmd,'cwd':str(root),'lean_path':str(root),'status':'PASS' if rc==0 else 'FAIL','exit_code':rc,'seconds':elapsed,'peak_child_rss_kib':resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss,'log_sha256':sha(out),'object_sha256':sha(obj.read_bytes()) if rc==0 and obj.exists() else None,'scope':'single-module compilation, not a complete K215 endpoint build'}
(logs/(key+'.json')).write_text(json.dumps(record,indent=2)+'\n');print(json.dumps(record,indent=2));print(out.decode(errors='replace'));raise SystemExit(rc)
