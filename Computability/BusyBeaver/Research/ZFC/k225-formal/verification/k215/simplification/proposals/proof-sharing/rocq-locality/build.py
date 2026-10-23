#!/usr/bin/env python3
"""Build the exact K215 runtime locality pilot, not the full ZFC endpoint.

Use: python3 build.py --out /fresh/directory
Optional: --repo /path/to/ProveIt to bind directly to an unchanged checkout
Coq 8.18.0 is the component toolchain used for the delivered receipt.
The maintained production gate remains Rocq 9.1.0 / stdlib 9.0.0.
"""
from pathlib import Path
import argparse, fcntl, hashlib, json, shutil, subprocess, time

HERE = Path(__file__).resolve().parent
PIN = 'cbf94cb552a3b49509e0eee80e7455d4eb5974c6'
PREFIX = Path('Computability/BusyBeaver/Research/ZFC/k225-formal')
VENDOR = PREFIX/'verification/k215/simplification/proposals/checked-transport/adapter/BusyCoq'
PROD = PREFIX/'rocq/rocq-extension/coq/215'

def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--repo',type=Path,help='Optional checkout; otherwise use the bundled exact dependencies')
    ap.add_argument('--out',type=Path)
    ap.add_argument('--check-sources',action='store_true',help='Verify dependency identities without invoking a proof compiler')
    ap.add_argument('--coqc',default='coqc')
    ap.add_argument('--coqchk',default='coqchk')
    ap.add_argument('--lock',type=Path,default=Path('/tmp/proveit-k215-proof-build.lock'))
    a=ap.parse_args()
    repo=a.repo.resolve() if a.repo else None
    provenance=json.loads((HERE/'provenance.json').read_text())
    selected=[]
    for entry in provenance['dependencies']:
        source=(repo/entry['repo_path']) if repo else (HERE/'deps'/entry['build_path'])
        if sha(source)!=entry['sha256']:
            raise SystemExit('Dependency hash mismatch: '+str(source))
        selected.append((source,entry['build_path'],entry['repo_path']))
    if a.check_sources:
        print('PASS: all eight dependency identities match the pinned source manifest')
        return
    if a.out is None: raise SystemExit('--out is required for a compiler build')
    out=a.out.resolve()
    if out.exists(): raise SystemExit('A fresh nonexistent output directory is required')
    out.mkdir(parents=True); (out/'logs').mkdir()
    mappings = [(str(VENDOR/f),f'BusyCoq/{f}') for f in ['LibTactics.v','Helper.v','TM.v']]
    mappings += [(str(PROD/f),f'K215F/{f}') for f in ['Table230.v','TM230.v','Zip.v','Boot230.v','Runtime230Core.v']]
    input_records=[]; files=[]
    for p,dest,source in selected:
        q=out/dest; q.parent.mkdir(parents=True,exist_ok=True); shutil.copyfile(p,q)
        files.append(dest); input_records.append({'repo_path':source,'build_path':dest,'sha256':sha(p),'bytes':p.stat().st_size})
    for name in ['FootprintReplay.v','Runtime215Locality.v']:
        shutil.copyfile(HERE/name,out/name); files.append(name)
        input_records.append({'local_path':name,'build_path':name,'sha256':sha(out/name),'bytes':(out/name).stat().st_size})
    options=['-Q','BusyCoq','BusyCoq','-Q','K215F','K215F']
    receipt={'expected_repository_pin':PIN,'scope':'exact K215 runtime component plus locality adapter; no ZFC endpoint replay',
      'toolchain':subprocess.check_output([a.coqc,'--version'],text=True),'inputs':input_records,'checks':[],'status':'IN_PROGRESS'}
    def save(): (out/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
    with a.lock.open('a') as lock:
        fcntl.flock(lock,fcntl.LOCK_EX)
        for name in files:
            command=[a.coqc,*options,name]; t=time.monotonic()
            p=subprocess.run(command,cwd=out,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True)
            log=out/'logs'/(name.replace('/','_')+'.log'); log.write_text(p.stdout)
            receipt['checks'].append({'source':name,'command':command,'exit_code':p.returncode,'elapsed_seconds':time.monotonic()-t,'log':str(log.relative_to(out)),'log_sha256':sha(log)})
            print(name,p.returncode,flush=True); save()
            if p.returncode:
                receipt['status']='FAILED';save();print(p.stdout,flush=True);raise SystemExit(p.returncode)
        command=[a.coqchk,'-silent',*options,'Runtime215Locality'];t=time.monotonic()
        p=subprocess.run(command,cwd=out,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True)
        log=out/'logs/coqchk.log';log.write_text(p.stdout)
        receipt['checks'].append({'command':command,'exit_code':p.returncode,'elapsed_seconds':time.monotonic()-t,'log':'logs/coqchk.log','log_sha256':sha(log)})
        receipt['objects']={str(p.relative_to(out)):sha(p) for p in sorted(out.rglob('*.vo'))}
        receipt['status']='PASS_COMPONENT' if p.returncode==0 else 'FAILED';save()
        print('coqchk',p.returncode,flush=True)
        raise SystemExit(p.returncode)
if __name__=='__main__':main()
