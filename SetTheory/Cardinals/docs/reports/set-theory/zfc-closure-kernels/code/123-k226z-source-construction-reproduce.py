#!/usr/bin/env python3
"""Rebuild every selected source/table and the two offset certificates."""
from pathlib import Path
import subprocess,sys,json,hashlib
HERE=Path(__file__).resolve().parent
def run(*args):
    result=subprocess.run([sys.executable,'-B',*map(str,args)],cwd=HERE,text=True,capture_output=True)
    print(result.stdout,end='')
    if result.returncode:
        print(result.stderr,file=sys.stderr,end='');raise SystemExit(result.returncode)
def main():
    run('build227.py');run('verify_roles.py');run('build226.py')
    run('build_offset_certificate.py')
    run('build_offset_certificate.py','--candidate','generated226/02_k226/sites.json','--out','offset_certificate226','--name','226')
    p=HERE/'generated226/02_k226/k226.tm'
    receipt={'status':'PORTABLE_K226_AND_K227_SOURCE_REPRODUCTION_PASS','canonical_k226_sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'steps':['exact227source/table','all-tape227roleproof','exact226source/table/quotient','offset227certificate','offset226certificate'],'scope':'Python construction and finite certificates. Run the separate Rocq and universal native proof drivers for their respective endpoints.'}
    (HERE/'reproduction.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt,indent=2))
if __name__=='__main__':
    if not __debug__:raise RuntimeError('Run with assertions enabled')
    main()
