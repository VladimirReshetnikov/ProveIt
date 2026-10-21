#!/usr/bin/env python3
"""Compile and recursively kernel-check CantorCredit.v in a fresh directory."""
import argparse, hashlib, json, pathlib, shutil, subprocess, time
p=argparse.ArgumentParser(); p.add_argument('--out',type=pathlib.Path,required=True)
a=p.parse_args(); out=a.out.resolve(); out.mkdir(parents=True,exist_ok=False)
src=pathlib.Path(__file__).with_name('CantorCredit.v'); shutil.copy2(src,out/src.name)
result={'source_sha256':hashlib.sha256(src.read_bytes()).hexdigest(),
        'toolchain':subprocess.check_output(['coqc','--version'],text=True).strip(),
        'steps':[]}
for cmd in [['coqc','CantorCredit.v'],['coqchk','-silent','CantorCredit']]:
    start=time.monotonic(); r=subprocess.run(['flock','/tmp/proveit-proof-compiler.lock',*cmd],cwd=out,capture_output=True,text=True)
    log=out/(cmd[0]+'.log'); log.write_text(r.stdout+r.stderr)
    result['steps'].append({'command':cmd,'exit_code':r.returncode,'elapsed_seconds':time.monotonic()-start,'log':log.name})
    if r.returncode:
        (out/'receipt.json').write_text(json.dumps(result,indent=2)+'\n'); print(r.stdout+r.stderr); raise SystemExit(r.returncode)
result['closed_assumption_reports']=(out/'coqc.log').read_text().count('Closed under the global context')
result['status']='COMPILED_AND_RECURSIVELY_KERNEL_CHECKED'
(out/'receipt.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
