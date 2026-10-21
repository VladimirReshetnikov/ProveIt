#!/usr/bin/env python3
"""Fresh serial build of the isolated ordinary K215 source proof.
Usage: python3 build.py --lean /absolute/path/to/lean
Requires the shipped Lean 4.32.0 core; no Lake/mathlib/network is needed.
Every source dependency in this packet is rebuilt once, in topological order.
"""
import argparse,hashlib,json,os,shutil,subprocess,time
from datetime import datetime,timezone
from pathlib import Path


def digest(path):return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
 p=argparse.ArgumentParser(description=__doc__)
 p.add_argument('--lean',default=shutil.which('lean'))
 p.add_argument('--target',default='BusyBeaver.ZFC.KSource215PlainAudit')
 p.add_argument('--output',type=Path)
 p.add_argument('--timeout',type=int,default=600)
 args=p.parse_args()
 if not args.lean:p.error('--lean is required if Lean is not on PATH')
 root=Path(__file__).resolve().parent
 output=(args.output or root/'fresh-build').resolve();output.mkdir(parents=True,exist_ok=True)
 lean=Path(args.lean).resolve();version=subprocess.check_output([str(lean),'--version'],text=True).strip()
 if 'version 4.32.0' not in version:raise RuntimeError('Expected Lean4.32.0; got '+version)
 seen=set();order=[]
 def source(name):return root/(name.replace('.','/')+'.lean')
 def visit(name):
  if name in seen:return
  seen.add(name)
  for line in source(name).read_text().splitlines():
   if line.startswith('import '):
    dep=line.removeprefix('import ').strip()
    if dep.startswith('BusyBeaver.'):
     visit(dep)
    elif dep!='Init':raise RuntimeError('unexpected external import '+dep)
  order.append(name)
 visit(args.target)
 if any('RMOffsetBisim' in name for name in order):raise RuntimeError('Offset module is unexpectedly in closure')
 env=dict(os.environ);env['LEAN_PATH']=str(output)
 records=[];run_at=datetime.now(timezone.utc).isoformat()
 for name in order:
  src=source(name);obj=output/(name.replace('.','/')+'.olean');obj.parent.mkdir(parents=True,exist_ok=True)
  command=[str(lean),'-o',str(obj),str(src)];start=time.monotonic()
  try:
   run=subprocess.run(command,cwd=root,env=env,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,timeout=args.timeout);rc=run.returncode;log=run.stdout
  except subprocess.TimeoutExpired as ex:rc=124;log=ex.stdout or b''
  if rc == 0 and (b'sorryAx' in log or b"declaration uses 'sorry'" in log):
   rc=1;log+=b'\nPortable build gate failed: incomplete proof or sorryAx was reported.\n'
  log_path=output/(name.replace('.','/')+'.log');log_path.write_bytes(log)
  record={'module':name,'source_sha256':digest(src),'object_sha256':digest(obj) if rc==0 else None,'status':'PASS' if rc==0 else 'FAIL','exit_code':rc,'seconds':time.monotonic()-start,'command':command,'log_sha256':hashlib.sha256(log).hexdigest()}
  records.append(record);print(name,record['status'],round(record['seconds'],3),'seconds',flush=True)
  (output/'result.json').write_text(json.dumps({'toolchain':version,'compiler_sha256':digest(lean),'started_at':run_at,'records':records,'scope':'ordinary K215 source-equivalence proof; binary endpoint not rebuilt'},indent=2)+'\n')
  if rc:print(log.decode(errors='replace'));raise SystemExit(rc)
 print('PASS: source-equivalence audit; no RMOffsetBisim dependency. Binary endpoint remains a separate build.')

if __name__=='__main__':main()
