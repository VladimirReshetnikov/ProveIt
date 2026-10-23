"""Owned serial invocation; exact frozen helper/map and exclusive raw receipts."""
from pathlib import Path
import argparse, hashlib, json, subprocess, time
p=argparse.ArgumentParser();p.add_argument('freeze',type=Path);p.add_argument('name');p.add_argument('--preflight',action='store_true');a=p.parse_args()
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
f=json.loads(a.freeze.read_bytes());D=a.freeze.resolve().parent
for path,h in f['files'].items():assert sha(path)==h,path
runner=Path(f['runner']);plan=Path(f['plan']);out=D/(a.name+'-run1');stdout=D/(a.name+'.stdout');stderr=D/(a.name+'.stderr');outer=D/(a.name+'-outer.json')
assert not any(p.exists()for p in[out,stdout,stderr,outer])
argv=['python3','-B',str(runner),'--map',str(plan),'--out',str(out)]
if a.preflight:argv.append('--check-plan')
start=time.monotonic()
with stdout.open('xb')as output,stderr.open('xb')as errors:r=subprocess.run(argv,stdout=output,stderr=errors)
receipt={'status':'PASS_EXIT_ZERO'if r.returncode==0 else'FAIL','exit_code':r.returncode,'seconds':time.monotonic()-start,'argv':argv,'stdout_sha256':sha(stdout),'stderr_sha256':sha(stderr),'freeze_sha256':sha(a.freeze),'launcher_sha256':sha(__file__)}
with outer.open('x')as output:json.dump(receipt,output,indent=2);output.write('\n')
print(json.dumps(receipt),flush=True);raise SystemExit(r.returncode)
