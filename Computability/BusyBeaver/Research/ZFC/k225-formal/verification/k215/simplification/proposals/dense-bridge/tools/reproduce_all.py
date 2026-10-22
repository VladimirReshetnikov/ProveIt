#!/usr/bin/env python3
"""Run the delivered focused proof checks in a new output tree.

Requires a pristine ProveIt checkout at the recorded revision, Lean 4.32.0,
and Coq 8.18 coqc/coqchk on PATH. Does not rebuild the complete K215 endpoint.
"""
import argparse
import json
from pathlib import Path
import shutil
import subprocess
import sys
import time

def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--repo',type=Path,required=True)
    p.add_argument('--lean',type=Path,required=True)
    p.add_argument('--out',type=Path,required=True)
    a=p.parse_args()
    root=Path(__file__).resolve().parents[1]
    repo,lean,out=a.repo.resolve(),a.lean.resolve(),a.out.resolve()
    if out.exists():
        raise SystemExit('The output directory must not exist.')
    subprocess.run([sys.executable,str(root/'tools/verify_packet.py')],check=True)
    out.mkdir(parents=True)
    # The semantic-interface driver writes beside itself. Run a private copy
    # so that distributed evidence is never overwritten.
    semantic=out/'semantic-interface'
    shutil.copytree(root/'semantic_interface',semantic)
    shutil.rmtree(semantic/'verification')
    rocq=out/'rocq-component'
    shutil.copytree(root/'rocq_shared',rocq)
    shutil.rmtree(rocq/'evidence')
    commands=[
        [sys.executable,str(root/'lean_logic/check_logic.py'),'--repo',str(repo),'--lean',str(lean),'--out',str(out/'logic')],
        [sys.executable,str(root/'dense_bridge/verify_dense_bridge.py'),'--repo',str(repo),'--lean',str(lean),'--work-dir',str(out/'dense')],
        [sys.executable,str(semantic/'verify.py'),'--repo',str(repo),'--lean',str(lean),'--compile'],
        [sys.executable,str(root/'tools/check_combined.py'),'--repo',str(repo),'--lean',str(lean),'--out',str(out/'combined')],
        [sys.executable,str(rocq/'reproduce.py'),'--out',str(out/'rocq')],
    ]
    records=[]
    for i,cmd in enumerate(commands,1):
        print('Checking component',i,'of',len(commands),flush=True)
        started=time.monotonic()
        with (out/f'component-{i}.log').open('w') as log:
            r=subprocess.run(cmd,stdout=log,stderr=subprocess.STDOUT)
        records.append({'component':i,'returncode':r.returncode,'seconds':round(time.monotonic()-started,3)})
        (out/'result.json').write_text(json.dumps({'scope':'Focused component checks; no full machine endpoint build.','records':records},indent=2)+'\n')
        if r.returncode:
            raise SystemExit(f'Component {i} failed; inspect its log in the output directory.')
    print('PASS: all focused components, the combined Lean closure, and recursive Rocq checks.',flush=True)

if __name__=='__main__':
    main()
