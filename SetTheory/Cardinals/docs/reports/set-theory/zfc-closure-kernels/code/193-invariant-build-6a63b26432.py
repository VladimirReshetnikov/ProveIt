#!/usr/bin/env python3
"""Fresh Lean 4.32.0 check of complete routed K215 residual coverage.

Required local input: a ProveIt checkout whose prerequisite sources match the
source-pins.json file (pinned base 57541fe0cfe3af62b4cb58747d8d1d7c16b338d5).
All 51 project modules are copied into a fresh isolated source/output directory
and compiled serially. No repository files are changed, no network is used, and
no precompiled project objects are reused. This is a runtime-component build,
not a complete ZFC endpoint build.
"""
from pathlib import Path
import argparse, fcntl, hashlib, json, os, re, shutil, subprocess, time

def sha(path): return hashlib.sha256(path.read_bytes()).hexdigest()

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--repo',type=Path,required=True)
    ap.add_argument('--lean',required=True)
    ap.add_argument('--out',type=Path,required=True)
    ap.add_argument('--lock',type=Path,default=Path('/tmp/proveit-k215-proof-build.lock'))
    args=ap.parse_args(); here=Path(__file__).resolve().parent
    repo=args.repo.resolve(); out=args.out.resolve(); src=out/'src'; objects=out/'objects'; logs=out/'logs'
    if out.exists() and any(out.iterdir()):raise RuntimeError('Use a fresh empty output directory')
    if out==repo or repo in out.parents:raise RuntimeError('Output must be outside the repository')
    for d in [src,objects,logs]:d.mkdir(parents=True,exist_ok=True)
    pins=json.loads((here/'source-pins.json').read_text())
    for name in pins['order']:
        pin=pins['modules'][name];rel=Path(*name.split('.')).with_suffix('.lean')
        source=(here/'lean'/rel) if pin['origin']=='new' else repo/pin['origin']
        if sha(source)!=pin['sha256']:raise RuntimeError('Source pin mismatch: '+str(source))
        target=src/rel;target.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(source,target)
    version=subprocess.run([args.lean,'--version'],check=True,capture_output=True,text=True).stdout.strip()
    if 'version 4.32.0,' not in version:raise RuntimeError('Expected Lean 4.32.0; got '+version)
    receipt={'base_commit':pins['head'],'compiler':version,'scope':'Fresh 51-module runtime component; no complete ZFC endpoint rebuild','all_passed':False,'modules':[]}
    for name in pins['order']:
        rel=Path(*name.split('.'));source=(src/rel).with_suffix('.lean');obj=(objects/rel).with_suffix('.olean');obj.parent.mkdir(parents=True,exist_ok=True)
        args.lock.parent.mkdir(parents=True,exist_ok=True)
        with args.lock.open('a+b') as lock:
            fcntl.flock(lock,fcntl.LOCK_EX)
            start=time.monotonic()
            run=subprocess.run([args.lean,'-j','1','-M','3072','-DmaxRecDepth=65536','-DmaxHeartbeats=8000000','-o',str(obj),str(source.relative_to(src))],cwd=src,env=dict(os.environ,LEAN_PATH=str(objects)),capture_output=True,text=True)
            elapsed=time.monotonic()-start
            fcntl.flock(lock,fcntl.LOCK_UN)
        text=run.stdout+run.stderr;log=logs/(name+'.log');log.write_text(text)
        audits=re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]",text)
        unexpected=sorted({a.strip() for _,xs in audits for a in xs.split(',') if a.strip() and a.strip() not in {'propext','Classical.choice','Quot.sound'}})
        receipt['modules'].append({'module':name,'source_sha256':sha(source),'exit_code':run.returncode,'seconds':elapsed,'log_sha256':sha(log),'object_sha256':sha(obj) if obj.exists() else None,'unexpected_axioms':unexpected})
        (out/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
        print(name,run.returncode,round(elapsed,3),flush=True)
        if run.returncode or unexpected:raise RuntimeError('Compiler/audit failure: '+name+'\n'+text)
    final=(logs/'BusyBeaver.ZFC.KResidualSites215.log').read_text()
    required=['all_sites','checked_leaf_suffixes','counts','covered','source_halts_iff']
    for theorem in required:
        if 'KResidualSites215.'+theorem not in final:raise RuntimeError('Missing named theorem audit '+theorem)
    receipt['all_passed']=True
    (out/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print('PASS: all 4,751 leaves and 6,176 guarded outcomes; component scope only.')

if __name__=='__main__': main()
