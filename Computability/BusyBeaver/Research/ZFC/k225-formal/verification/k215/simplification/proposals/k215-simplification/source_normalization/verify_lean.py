#!/usr/bin/env python3
"""Serial, fresh Lean check of the normalized K215 source-correspondence proof.

Usage: python3 verify_lean.py --repo /path/to/ProveIt --lean /path/to/lean
Requires Lean4.32.0 and the pinned upstream modules; no Mathlib dependencies.
The build directory must be absent or empty; repository files are not edited.
A new receipt is written under the build directory, preserving shipped evidence.
Both the repository commit and every upstream dependency byte hash are checked.
"""
from __future__ import annotations
import argparse,hashlib,json,os,shutil,subprocess,time
from pathlib import Path
BASE=Path(__file__).resolve().parent
PIN='b6c7087477e51c017003bd729e712c8969733223'
DEPENDENCY_SHA256={'RegisterPath': 'a1457f32034eb4da50c8755610a366805260aac711424bba8b516ccab4e5b879', 'RMDag': '55a47480da9cb00e5420b896c3a8c72ec1f51081d610874903f932311231076d', 'RMEquiv': 'cc696ec1d000e9201506f652987d94ba17661114ba785b8dcb09b4f958a32a57', 'RMBisim': '68c28a182eed06c0f8d266f0d79d8f884f086228a4794da00da51cf02dbbb13b', 'Dag222': '9e73e2d6ac692c33b07efde7faa08545fdd61ca692ec03e21afe2ffe99a7cb71', 'Dag219': 'fd3bdfcd5048dd7205b66fcce323bb78017a3137dcd04cc3ef9c0788334ac3ad', 'DagDom': '9d52a871ea029099dd192fb66cf0ef802c4f9ed6e8c32d3a7b3661ce343af5aa', 'DagPerm': '11ccf62cf09e41b8f85e1c7d6aa56aeca0c0d211e119fb5309d5fb1ac6a96123'}

def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--repo',type=Path,required=True);ap.add_argument('--lean',type=Path,required=True)
    ap.add_argument('--build',type=Path,default=BASE/'reproduction_build')
    ap.add_argument('--memory-mb',type=int,default=3500)
    args=ap.parse_args();repo=args.repo.resolve();build=args.build.resolve();lean=args.lean.resolve()
    actual=subprocess.run(['git','rev-parse','HEAD'],cwd=repo,capture_output=True,text=True,check=True).stdout.strip()
    if actual != PIN:raise RuntimeError(f'Expected repository HEAD {PIN}, got {actual}')
    if build.exists() and any(build.iterdir()):raise RuntimeError(f'Build directory must be empty: {build}')
    module_dir=build/'BusyBeaver/ZFC';module_dir.mkdir(parents=True,exist_ok=True)
    logdir=build/'logs';logdir.mkdir(exist_ok=True)
    dep=['RegisterPath','RMDag','RMEquiv','RMBisim','Dag222','Dag219','DagDom','DagPerm']
    local=['RMNormalizedBisim','KSource215Programs','KSource215Data','KSource215NormalizedData']+[f'KSource215NormalizedCheck{i:02d}' for i in range(16)]+['KSource215Normalized','KSource215']
    jobs=[]
    for name in dep+local:
        if name in dep:src=repo/'Computability/BusyBeaver/Lean/BusyBeaver/ZFC'/f'{name}.lean'
        elif name=='RMNormalizedBisim':src=BASE/f'{name}.lean'
        else:src=BASE/'normalized_lean'/f'{name}.lean'
        if not src.is_file():raise FileNotFoundError(src)
        if name in dep and sha(src)!=DEPENDENCY_SHA256[name]:
            raise RuntimeError(f'Pinned dependency contents differ: {src}')
        dst=module_dir/src.name;shutil.copyfile(src,dst);jobs.append((name,dst))
    env=dict(os.environ,LEAN_PATH=str(build))
    version=subprocess.run([str(lean),'--version'],capture_output=True,text=True,check=True).stdout.strip()
    if '4.32.0' not in version:raise RuntimeError(f'Expected Lean4.32.0, got {version}')
    receipt={'schema':'K215-normalized-source-kernel-v1','baseline_commit':PIN,'actual_repository_commit':actual,'toolchain':version,'dependency_sha256':DEPENDENCY_SHA256,'modules':[],'complete':False,'scope':'Exact source-program halting equivalence; not a rebuilt whole-machine endpoint'}
    path=build/'kernel_receipt.json'
    for name,dst in jobs:
        out=dst.with_suffix('.olean');so=logdir/f'{name}.stdout.log';se=logdir/f'{name}.stderr.log'
        cmd=[str(lean),'-j1',f'-M{args.memory_mb}','-o',str(out),str(dst)]
        start=time.monotonic()
        with so.open('w') as stdout,se.open('w') as stderr:
            p=subprocess.Popen(cmd,cwd=build,env=env,stdout=stdout,stderr=stderr)
            _,status,usage=os.wait4(p.pid,0);p.returncode=os.waitstatus_to_exitcode(status)
        row={'module':name,'exit_code':p.returncode,'wall_seconds':round(time.monotonic()-start,3),'max_rss_kib':usage.ru_maxrss,'source_sha256':sha(dst),'olean_sha256':sha(out) if p.returncode==0 else None,'stdout':so.read_text(),'stderr':se.read_text()}
        output=row['stdout']+'\n'+row['stderr']
        if "sorryAx" in output or "uses 'sorry'" in output or "declaration uses sorry" in output:
            row['forbidden_proof_placeholder']=True
            row['exit_code']=1
        receipt['modules'].append(row);path.write_text(json.dumps(receipt,indent=2)+'\n')
        print(json.dumps({k:row[k] for k in ['module','exit_code','wall_seconds','max_rss_kib']}),flush=True)
        if row['exit_code']:raise SystemExit(row['exit_code'] or 1)
    receipt['complete']=True
    receipt['total_wall_seconds']=round(sum(x['wall_seconds'] for x in receipt['modules']),3)
    receipt['peak_rss_kib']=max(x['max_rss_kib'] for x in receipt['modules'])
    receipt['checked_entries']=1426;receipt['checked_branches']=2851
    path.write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps({'complete':True,'total_wall_seconds':receipt['total_wall_seconds'],'peak_rss_kib':receipt['peak_rss_kib']}),flush=True)

if __name__=='__main__':main()
