from pathlib import Path
import argparse
import fcntl
import hashlib
import json
import os
import re
import subprocess
import tempfile
import time

HERE=Path(__file__).resolve().parent
parser=argparse.ArgumentParser(description='Freshly compile the self-contained semantic KSim prototype and typed API audit.')
parser.add_argument('--lean',required=True,help='Path to the Lean 4.32.0 executable')
parser.add_argument('--out',type=Path,default=HERE/'verification',help='New build/log/receipt directory')
parser.add_argument('--lock',type=Path,default=Path(tempfile.gettempdir())/'proveit-k215-proof-build.lock')
args=parser.parse_args()
LEAN=Path(args.lean).resolve()
SRC=HERE/'formal'
OUT=args.out.resolve()
BUILD=OUT/'build'
LOGS=OUT/'logs'
seen=set();order=[]
def visit(m):
    if m in seen:return
    seen.add(m)
    rel=Path(m.replace('.','/')+'.lean')
    p=SRC/rel
    if not p.exists():
        assert m=='Init',f'Missing source dependency: {m}'
        return
    for dep in re.findall(r'^import\s+(\S+)',p.read_text(),re.M):visit(dep)
    order.append(m)
visit('BusyBeaver.ZFC.KSim')
if (SRC/'SemanticAudit.lean').exists():order.append('SemanticAudit')
OUT.mkdir(parents=True,exist_ok=True)
if BUILD.exists() or LOGS.exists():
    raise SystemExit('Use a new --out directory: compilation must start from fresh objects.')
BUILD.mkdir();LOGS.mkdir()
env=os.environ.copy();env['LEAN_PATH']=str(BUILD)
records=[]
lock=open(args.lock,'w')
fcntl.flock(lock,fcntl.LOCK_EX)
print('Acquired serial proof compiler lock',flush=True)
version=subprocess.check_output([str(LEAN),'--version'],text=True).strip()
if 'version 4.32.0' not in version:
    raise SystemExit(f'Expected Lean 4.32.0, got: {version}')
for m in order:
    rel=Path(m.replace('.','/'))
    source=SRC/rel.with_suffix('.lean')
    target=BUILD/rel.with_suffix('.olean')
    target.parent.mkdir(parents=True,exist_ok=True)
    log=LOGS/(m+'.log')
    print('Building '+m,flush=True)
    start=time.monotonic()
    command=[str(LEAN),'-j1','-M8192','-o',str(target),str(rel.with_suffix('.lean'))]
    with log.open('w') as f:
        p=subprocess.run(command,cwd=SRC,env=env,stdout=f,stderr=subprocess.STDOUT)
    record={'module':m,'source_sha256':hashlib.sha256(source.read_bytes()).hexdigest(),
            'command':command,'returncode':p.returncode,'seconds':time.monotonic()-start,
            'log_sha256':hashlib.sha256(log.read_bytes()).hexdigest()}
    if p.returncode==0:
        record['object_sha256']=hashlib.sha256(target.read_bytes()).hexdigest()
    records.append(record)
    (OUT/'build_result.json').write_text(json.dumps({'status':'PASS' if p.returncode==0 and m==order[-1] else 'IN_PROGRESS' if p.returncode==0 else 'FAIL','lean_version':version,'compiler_sha256':hashlib.sha256(LEAN.read_bytes()).hexdigest(),'source_root':str(SRC),'scope':'Fresh 13-module KSim closure and typed API audit; not a full K215 endpoint build.','records':records},indent=2)+'\n')
    print(f'{m}: exit {p.returncode} in {record["seconds"]:.3f}s',flush=True)
    if p.returncode:
        print(log.read_text(),flush=True)
        raise SystemExit(p.returncode)
print('PASS',flush=True)
