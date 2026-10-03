#!/usr/bin/env python3
"""Bounded identity/type tests; no tampered scientific payload is executed."""
from pathlib import Path
import argparse, hashlib, json, shutil, subprocess, sys, tempfile
ROOT=Path(__file__).resolve().parent

def check(condition,message):
    if not condition:raise RuntimeError(message)

def invoke(root,*args):
    return subprocess.run([sys.executable,'-I','-B',str(root/'replay.py'),*args],capture_output=True,text=True,timeout=60)

def main():
    p=argparse.ArgumentParser();p.add_argument('--output-dir',type=Path,required=True);a=p.parse_args();out=a.output_dir.resolve()
    check(out!=ROOT and ROOT not in out.parents,'Output must be external')
    check(not out.exists() or (out.is_dir() and not any(out.iterdir())),'Output must be absent or empty')
    check(invoke(ROOT,'--verify-only').returncode==0,'Original payload failed identity verification')
    out.mkdir(parents=True,exist_ok=True);results=[]
    for case in ['modified-code','missing-certificate','modified-certificate-and-public-checksums','unexpected-file']:
        with tempfile.TemporaryDirectory(prefix='report31-tamper-') as tmp:
            copy=Path(tmp)/'payload';shutil.copytree(ROOT,copy,copy_function=shutil.copy2)
            if case=='modified-code':
                f=copy/'scientific/code/component_rule.py';f.write_bytes(f.read_bytes()+b'\n# tamper probe\n')
            elif case=='missing-certificate':(copy/'scientific/local-quartic-certificate.json').unlink()
            elif case=='modified-certificate-and-public-checksums':
                f=copy/'scientific/local-quartic-certificate.json';f.write_bytes(f.read_bytes()+b' ')
                (copy/'SHA256SUMS').write_text(''.join(hashlib.sha256(q.read_bytes()).hexdigest()+'  '+q.relative_to(copy).as_posix()+'\n' for q in sorted(copy.rglob('*')) if q.is_file() and q.name!='SHA256SUMS'))
            else:(copy/'unexpected.txt').write_text('unexpected')
            done=invoke(copy,'--verify-only');check(done.returncode!=0,'Tampered payload was accepted: '+case)
            check('mismatch' in done.stderr,'Tamper did not fail at identity gate: '+case)
            results.append({'case':case,'identity_gate_rejected':True})
    done=invoke(ROOT,'--self-test-types');check(done.returncode==0,'Strict type regression failed')
    summary={'status':'PASS','tamper_cases':results,'types':json.loads(done.stdout),'scientific_code_executed_on_tampered_payload':False}
    (out/'tamper-summary.json').write_text(json.dumps(summary,indent=2,sort_keys=True)+'\n');print(json.dumps(summary,indent=2,sort_keys=True))
if __name__=='__main__':main()
