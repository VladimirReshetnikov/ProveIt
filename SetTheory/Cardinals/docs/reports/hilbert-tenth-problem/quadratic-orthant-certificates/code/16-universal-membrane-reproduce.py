#!/usr/bin/env python3
"""Verify both source manifests, regenerate all computational deliverables in a
clean temporary copy, run every public checker, and compare saved output bytes.
Python 3 standard library only. The source release is never modified.
"""
from pathlib import Path
import argparse, hashlib, json, os, shutil, subprocess, sys, tempfile
ROOT=Path(__file__).resolve().parent

def digest(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()

def check_manifest(root):
    m=json.loads((root/'MANIFEST.json').read_text())
    for f in m['files']:
        p=root/f['path']
        assert p.is_file(),f"Missing manifest entry: {f['path']}"
        assert p.stat().st_size==f['bytes'],f"Length mismatch: {f['path']}"
        assert digest(p)==f['sha256'],f"Hash mismatch: {f['path']}"
    return m

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--receipt',type=Path,help='Optional output path for the deterministic receipt')
    args=ap.parse_args()
    commands={
      'packet':[
        ['build_frontend.py'],['verify_frontend.py'],['verify_membrane.py'],
        ['replay_example.py'],['verify_density.py'],
        ['quadratic_outcome.py','--steps','1'],['verify_quadratic.py'],
      ],
      'direct':[
        ['build_direct.py'],['verify_direct.py'],['build_quadratic.py','--steps','1'],
        ['make_accepting_witness.py'],['verify_accepting_quadratic.py'],['verify_membrane.py'],
      ],
    }
    manifests={name:check_manifest(ROOT/name) for name in commands}
    checks=[]
    with tempfile.TemporaryDirectory(prefix='membrane-reproduction-') as tmp:
        work=Path(tmp)
        for name in commands:
            shutil.copytree(ROOT/name,work/name,ignore=shutil.ignore_patterns('__pycache__','*.pyc'))
        env=dict(os.environ,PYTHONDONTWRITEBYTECODE='1',PYTHONHASHSEED='0')
        for name,steps in commands.items():
            for cmd in steps:
                print(f"Checking {name}/{' '.join(cmd)}",file=sys.stderr,flush=True)
                result=subprocess.run([sys.executable,*cmd],cwd=work/name,env=env,text=True,capture_output=True)
                if result.returncode:
                    raise RuntimeError(f"{name}/{' '.join(cmd)} failed:\n{result.stdout}\n{result.stderr}")
                checks.append({'packet':name,'command':['python3',*cmd],'status':'passed'})
            loader=['load_input.py','--A','64'] if name=='packet' else ['load_input.py','6','0']
            result=subprocess.run([sys.executable,*loader],cwd=work/name,env=env,text=True,capture_output=True,check=True)
            saved='input64.json' if name=='packet' else 'input6_0.json'
            assert json.loads(result.stdout)==json.loads((ROOT/name/saved).read_text()),f'{name} loader mismatch'
            count=0
            for entry in manifests[name]['files']:
                f=entry['path']
                assert (work/name/f).read_bytes()==(ROOT/name/f).read_bytes(),f'Non-reproducible file: {name}/{f}'
                count+=1
            checks.append({'packet':name,'check':'all source-manifest entries unchanged after regeneration','files':count,'status':'passed'})
    receipt={
      'status':'passed',
      'source_manifest_sha256':{name:digest(ROOT/name/'MANIFEST.json') for name in commands},
      'checks':checks,
      'scope':'Clean temporary-copy regeneration, all public computational checks, source-manifest verification, and exact byte comparison. Mathematical all-input claims require the article proofs; this receipt is not formal proof-assistant verification.'
    }
    out=json.dumps(receipt,indent=2)+'\n'
    if args.receipt:
        args.receipt.parent.mkdir(parents=True,exist_ok=True);args.receipt.write_text(out)
    print(out,end='')
if __name__=='__main__':main()
