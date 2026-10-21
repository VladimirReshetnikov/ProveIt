#!/usr/bin/env python3
"""Compile exact lookup-cost theorems after reproduce.py built their prerequisites."""
import argparse,hashlib,json,shutil,subprocess,time
from pathlib import Path
ROOT=Path(__file__).resolve().parent
ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--build',type=Path,required=True);a=ap.parse_args()
out=a.build.resolve();work=out/'work';logs=out/'logs'
receipt=json.loads((out/'receipt.json').read_text())
if not receipt['complete']:raise SystemExit('Build the source theorem first')
for item in receipt['sources']:
 p=work/item['module']
 if hashlib.sha256(p.read_bytes()).hexdigest()!=item['compiled_source_sha256']:raise SystemExit('Changed prerequisite source: '+str(p))
shutil.copy2(ROOT/'LookupCost215.v',work/'LookupCost215.v')
cmd=['coqc','-Q','deps/K230','K230','-Q','deps/K230P','K230P','-Q','deps/K215F','K215F','LookupCost215.v']
t=time.monotonic();p=subprocess.run(cmd,cwd=work,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True)
log=logs/'LookupCost215.v.log';log.write_text(p.stdout)
r={'command':cmd,'exit_code':p.returncode,'seconds':round(time.monotonic()-t,3),'closed_reports':p.stdout.count('Closed under the global context'),'source_sha256':hashlib.sha256((ROOT/'LookupCost215.v').read_bytes()).hexdigest(),'log_sha256':hashlib.sha256(log.read_bytes()).hexdigest(),'scope':'Exact component accounting; not timing or complete endpoint verification'}
(out/'metrics_receipt.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(r,indent=2));print(p.stdout)
if p.returncode or r['closed_reports']!=3 or 'Axioms:' in p.stdout:raise SystemExit(1)
