#!/usr/bin/env python3
"""Portable bounded replay. Reads this release and writes only a temporary copy."""
import argparse, hashlib, json, os, shutil, subprocess, sys, tempfile, time
from pathlib import Path
if sys.flags.optimize:
    raise SystemExit('ERROR: -O / PYTHONOPTIMIZE is unsupported: some audit helpers use assertions.')
ROOT=Path(__file__).resolve().parent

def check(ok,message):
    if not ok:raise RuntimeError(message)
def sha(path):return hashlib.sha256(path.read_bytes()).hexdigest()
def contained(root,name):
    check(isinstance(name,str) and not Path(name).is_absolute(),'Invalid relative path')
    p=(root/name).resolve();check(root.resolve() in p.parents,'Path escapes bundle: '+name)
    return p

def verify_manifest():
    manifest=json.loads((ROOT/'MANIFEST.json').read_text())
    expected={item['path'] for item in manifest['files']}
    actual={str(p.relative_to(ROOT)) for p in ROOT.rglob('*') if p.is_file() and p.name!='MANIFEST.json'}
    check(expected==actual,'Manifest file set mismatch: '+str(sorted(expected^actual)))
    for item in manifest['files']:
        p=contained(ROOT,item['path']);check(not p.is_symlink(),'Symlink in release: '+item['path'])
        check(p.stat().st_size==item['bytes'] and sha(p)==item['sha256'],'Manifest hash mismatch: '+item['path'])
    return manifest

def verify_pins():
    r=ROOT/'evidence/diophantine_zfc_round2/review'
    pins=json.loads((r/'SOURCE_PINS.json').read_text())
    for item in pins['files']:
        p=contained(r,item['local_path'])
        check(p.is_file() and sha(p)==item['local_sha256'],'Received-source pin mismatch: '+item['local_path'])
        check(p.stat().st_size==item['bytes'],'Received-source byte length mismatch')
    old=ROOT/'evidence/diophantine_zfc_review';pins2=json.loads((old/'SOURCE_PINS.json').read_text())
    for item in pins2['files']:
        p=contained(old,item['local_name']);data=p.read_bytes()
        check(sha(p)==item['sha256'],'Prior-source SHA256 mismatch')
        blob=hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()
        check(blob==item['git_blob_sha1'],'Prior-source git blob mismatch')
    check(sha(ROOT/'evidence/diophantine_zfc_compiler/k215.tm')=='fdbcef0825886035c3091c8537a69535bc96f9e265f0ae45863543d40ae70090','K215 table mismatch')
    return len(pins['files']),len(pins2['files'])

def normalize(x):
    if isinstance(x,dict):return {k:sorted(v) if k=='coefficient_ports' else normalize(v) for k,v in x.items()}
    if isinstance(x,list):return [normalize(v) for v in x]
    return x

def compare_json(a,b):
    check(normalize(json.loads(a.read_text()))==normalize(json.loads(b.read_text())),'Reproduced JSON differs: '+str(b))

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--exhaustive',action='store_true',help='Also compile/run the owned C++17 exhaustive center/pair counter (requires c++).')
    ap.add_argument('--cxx',default='c++',help='C++ compiler executable for --exhaustive; default c++.')
    args=ap.parse_args()
    start=time.monotonic();before=verify_manifest();a,b=verify_pins()
    print(f'PASS manifest ({len(before["files"])} files); source pins ({a} current, {b} prior)',flush=True)
    with tempfile.TemporaryDirectory(prefix='combined-con-zfc-checks-') as td:
        tmp=Path(td)/'release';shutil.copytree(ROOT,tmp)
        work=tmp/'evidence/diophantine_zfc_round2'
        env=os.environ.copy();env.pop('PYTHONOPTIMIZE',None);env['PYTHONDONTWRITEBYTECODE']='1';env['PYTHONHASHSEED']='0'
        def run(label,args):
            began=time.monotonic()
            p=subprocess.run(args,cwd=tmp,env=env,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,timeout=600)
            if p.returncode:
                print(p.stdout,file=sys.stderr);raise RuntimeError(label+' failed with status '+str(p.returncode))
            print(f'PASS {label} ({time.monotonic()-began:.1f}s)',flush=True)
            return p.stdout
        py=lambda p:[sys.executable,'-B',str(p)]
        if args.exhaustive:
            binary=Path(td)/'count-windows'
            run('compile owned C++17 counter',[args.cxx,'-std=c++17','-O2',str(work/'compiler/count_windows_independent.cpp'),'-o',str(binary)])
            output=run('exhaustive center/pair counter',[str(binary),str(tmp/'evidence/diophantine_zfc_compiler/k215.tm')])
            p=work/'compiler/count_windows_independent.json';p.write_text(output)
            compare_json(p,ROOT/'evidence/diophantine_zfc_round2/compiler/count_windows_independent.json')
        stages=[('received-circuit inert-JSON review','review/independent_circuit_review.py',['review/independent_circuit_review.json']),
                ('14-variable norm elimination','pell/build_start_only14.py',['pell/start_only14_polynomial75.json','pell/start_only14_system69.json','pell/start_only14_arithmetic_audit.json']),
                ('ordinary-strong and root-shear identities','pell/build_sheared_tradeoffs.py',[]),
                ('sparse low-degree identities','quadratic/independent_sparse_audit.py',['quadratic/independent_sparse_audit.json']),
                ('raw-machine coefficient checks','compiler/raw_coefficients_audit.py',['compiler/raw_coefficients_audit.json','compiler/raw_coefficients_specification.json'])]
        for label,script,outputs in stages:
            run(label,py(work/script))
            if script=='pell/build_sheared_tradeoffs.py':
                outputs=['pell/'+p.name for p in (ROOT/'evidence/diophantine_zfc_round2/pell').glob('*.json') if p.name.startswith(('start_only_ordinary','start_only_sheared','sheared_tradeoff'))]
            for out in outputs:compare_json(work/out,ROOT/'evidence/diophantine_zfc_round2'/out)
        run('independent integer lifts and all final forms',py(tmp/'checks/check_final_forms.py'))
        compare_json(work/'integers/INDEPENDENT_INTEGER_AUDIT.json',ROOT/'evidence/diophantine_zfc_round2/integers/INDEPENDENT_INTEGER_AUDIT.json')
        compare_json(tmp/'FINAL_CHECKS.json',ROOT/'FINAL_CHECKS.json')
        run('displayed report equation transcription',py(tmp/'report/check_report_equations.py'))
        compare_json(tmp/'report/REPORT_EQUATION_CHECK.json',ROOT/'report/REPORT_EQUATION_CHECK.json')
    check(verify_manifest()==before,'Release changed during replay')
    print(f'PASS all bounded checks ({time.monotonic()-start:.1f}s); release untouched.',flush=True)
    print('Scope: exact finite algebra and bounded compiler checks, not a proof of Con(ZFC), a halting search, or a new end-to-end proof-assistant build.')
if __name__=='__main__':
    try:main()
    except (OSError,ValueError,RuntimeError,subprocess.TimeoutExpired) as exc:
        print('FAIL: '+str(exc),file=sys.stderr);raise SystemExit(1)
